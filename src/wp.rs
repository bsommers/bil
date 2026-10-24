use crate::ast::*;
use crate::eval::{Interpreter, Value};
pub use crate::expr_utils::{extract_int_constants, format_expr_concise, free_vars, subst_expr};
use crate::ontology::OntologyRegistry;
use crate::smt::{
    attach_model, emit_vc_smt2, emit_vc_smt2_header, evaluate_vc_agreement, vc_to_smt,
    parse_smt_model, run_smt_incremental_batch_with_prover, run_smt_prover, AgreementOutcome,
    Prover, ProverResult, Verdict,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Status {
    Proved { by: String },
    Refuted { counterexample: String },
    /// `samples` assignments were evaluated out of a space of `space` (equal when exhaustive).
    BoundedOnly { samples: usize, space: usize },
    Unknown { reason: String },
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Status::Proved { by } => write!(f, "PROVED (by {})", by),
            Status::Refuted { .. } => write!(f, "REFUTED"),
            Status::BoundedOnly { samples, space } if space > samples => {
                write!(f, "BOUNDED ({} of {} samples)", samples, space)
            }
            Status::BoundedOnly { samples, .. } => write!(f, "BOUNDED ({} samples)", samples),
            Status::Unknown { reason } => write!(f, "UNKNOWN ({})", reason),
        }
    }
}

pub fn decide_status(
    bounded_ce: Option<String>,
    samples: usize,
    smt: Option<&ProverResult>,
) -> Status {
    decide_status_sampled(bounded_ce, Samples { evaluated: samples, space: samples }, smt)
}

/// [`decide_status`] for a bounded check that may have sampled only part of its space.
pub fn decide_status_sampled(
    bounded_ce: Option<String>,
    samples: Samples,
    smt: Option<&ProverResult>,
) -> Status {
    let Samples { evaluated, space } = samples;
    if let Some(ce) = bounded_ce {
        return Status::Refuted { counterexample: ce };
    }
    match smt.map(|r| (&r.verdict, r.prover.as_str(), r.stdout.as_str(), r.detail.as_str())) {
        Some((Verdict::Inconsistent, prover, _, _)) => Status::Proved {
            by: prover.to_string(),
        },
        Some((Verdict::Consistent, _, stdout, _)) => Status::Refuted {
            counterexample: parse_smt_model(stdout)
                .unwrap_or_else(|| format!("SMT model: {}", stdout.trim())),
        },
        Some((Verdict::Skipped, _, _, _)) | Some((Verdict::Unknown, _, _, _)) | None
            if evaluated > 0 =>
        {
            Status::BoundedOnly {
                samples: evaluated,
                space,
            }
        }
        Some((_, _, _, detail)) => Status::Unknown {
            reason: detail.to_string(),
        },
        None => Status::Unknown {
            reason: "no solver and no samples".into(),
        },
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ObligationKind {
    IfFiGuardTotality,
    IfFiBranchPostcondition(usize),
    DoOdInitialization,
    DoOdPreservation(usize),
    DoOdVariantNonNegative(usize),
    DoOdVariantDecrease(usize),
    DoOdExitPostcondition,
    FunctionContract,
    RefinementPrecondition(String),
    RefinementPostcondition(String),
    ProofLemma,
}

impl fmt::Display for ObligationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ObligationKind::IfFiGuardTotality => write!(f, "if..fi Guard Totality (BB = ∨ Gi)"),
            ObligationKind::IfFiBranchPostcondition(i) => {
                write!(f, "if..fi Branch #{} Postcondition (G{} => wp(S{}, Q))", i + 1, i + 1, i + 1)
            }
            ObligationKind::DoOdInitialization => {
                write!(f, "do..od Invariant Initialization (Pre => I)")
            }
            ObligationKind::DoOdPreservation(i) => {
                write!(f, "do..od Invariant Preservation Branch #{} (I ∧ G{} => wp(S{}, I))", i + 1, i + 1, i + 1)
            }
            ObligationKind::DoOdVariantNonNegative(i) => {
                write!(f, "do..od Variant Non-Negativity Branch #{} (I ∧ G{} => V >= 0)", i + 1, i + 1)
            }
            ObligationKind::DoOdVariantDecrease(i) => {
                write!(f, "do..od Variant Strict Decrease Branch #{} (I ∧ G{} => wp(S{}, V < V0))", i + 1, i + 1, i + 1)
            }
            ObligationKind::DoOdExitPostcondition => {
                write!(f, "do..od Exit Correctness (I ∧ ¬BB => Post)")
            }
            ObligationKind::FunctionContract => {
                write!(f, "Function Contract (Pre => wp(Body, Post))")
            }
            ObligationKind::RefinementPrecondition(spec) => {
                write!(f, "Refinement Weakened Precondition (Pre_{} => Pre_impl)", spec)
            }
            ObligationKind::RefinementPostcondition(spec) => {
                write!(f, "Refinement Strengthened Postcondition (Post_impl => Post_{})", spec)
            }
            ObligationKind::ProofLemma => {
                write!(f, "Verus Ghost Proof Lemma ((Requires ∧ Body) => Ensures)")
            }
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct ProofObligation {
    pub fn_name: String,
    pub kind: ObligationKind,
    pub formula_desc: String,
    pub status: Status,
    pub verified: bool,
    pub counterexample: Option<String>,
    pub smt_prover: Option<String>,
    pub smt_verdict: Option<Verdict>,
    pub agreement: Option<AgreementOutcome>,
    pub smt2_script: Option<String>,
}

/// Peels top-level `let x = v in body` bindings by substituting `x := v` into `body`,
/// allowing structural GCL obligations (`if..fi`, `do..od`) inside `let` bindings to be verified.
fn peel_let_bindings(expr: &Expr) -> Expr {
    match expr {
        Expr::LetIn { name, value, body } => {
            let mut map = BTreeMap::new();
            map.insert(name.clone(), (**value).clone());
            let substituted = subst_expr(body, &map);
            peel_let_bindings(&substituted)
        }
        other => other.clone(),
    }
}

fn conj(a: Expr, b: Expr) -> Expr {
    if a == Expr::Bool(true) {
        return b;
    }
    if b == Expr::Bool(true) {
        return a;
    }
    Expr::Binary {
        op: BinOp::And,
        left: Box::new(a),
        right: Box::new(b),
    }
}

fn disj(a: Expr, b: Expr) -> Expr {
    if a == Expr::Bool(false) {
        return b;
    }
    if b == Expr::Bool(false) {
        return a;
    }
    Expr::Binary {
        op: BinOp::Or,
        left: Box::new(a),
        right: Box::new(b),
    }
}

fn implies(a: Expr, b: Expr) -> Expr {
    if a == Expr::Bool(false) || b == Expr::Bool(true) {
        return Expr::Bool(true);
    }
    Expr::Binary {
        op: BinOp::Implies,
        left: Box::new(a),
        right: Box::new(b),
    }
}

fn not(a: Expr) -> Expr {
    Expr::Unary {
        op: UnaryOp::Not,
        expr: Box::new(a),
    }
}

/// Computes `wp(branch_body, post)` under Dijkstra's predicate transformer calculus
fn wp_branch_body(body: &GclBody, post: &Expr, default_var: Option<&str>) -> Expr {
    match body {
        GclBody::Skip => post.clone(),
        GclBody::Abort => Expr::Bool(false),
        GclBody::Updates(ups) => {
            let mut map = BTreeMap::new();
            for (v, e) in ups {
                map.insert(v.clone(), e.clone());
            }
            subst_expr(post, &map)
        }
        GclBody::Expr(e) => {
            let mut map = BTreeMap::new();
            if let Some(dv) = default_var {
                map.insert(dv.to_string(), e.clone());
            }
            map.insert("result".to_string(), e.clone());
            subst_expr(post, &map)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn build_vc_obligation(
    program: &Program,
    ontology: &OntologyRegistry,
    fn_name: &str,
    kind: ObligationKind,
    fn_params: &[Param],
    state_params: &[Param],
    vc: &Expr,
    include_axioms: bool,
    proved_lemmas: &[ProofDecl],
    run_smt: bool,
) -> ProofObligation {
    let (bounded_ok, ce, samples) =
        check_vc_bounded(program, ontology, fn_params, state_params, vc);

    let mut all_params = Vec::new();
    let mut seen = BTreeSet::new();
    for p in fn_params.iter().chain(state_params.iter()) {
        if seen.insert(p.name.clone()) {
            all_params.push(p.clone());
        }
    }

    let smt2_script = emit_vc_smt2(
        program,
        ontology,
        &all_params,
        vc,
        include_axioms,
        proved_lemmas,
    );
    let smt_res = if run_smt {
        smt2_script
            .as_ref()
            .map(|script| attach_model(run_smt_prover(Prover::Auto, script), script))
    } else {
        None
    };
    let (smt_prover, smt_verdict, agreement) = if let Some(ref res) = smt_res {
        let agr = evaluate_vc_agreement(bounded_ok, res.verdict);
        (Some(res.prover.clone()), Some(res.verdict), Some(agr))
    } else {
        (None, None, None)
    };

    let status = decide_status_sampled(ce.clone(), samples, smt_res.as_ref());
    let verified = matches!(status, Status::Proved { .. } | Status::BoundedOnly { .. });
    let counterexample = match &status {
        Status::Refuted { counterexample } => Some(counterexample.clone()),
        _ => ce,
    };

    ProofObligation {
        fn_name: fn_name.to_string(),
        kind,
        formula_desc: format_expr_concise(vc),
        status,
        verified,
        counterexample,
        smt_prover,
        smt_verdict,
        agreement,
        smt2_script,
    }
}

#[allow(clippy::too_many_arguments)]
fn build_vc_obligations_batch(
    program: &Program,
    ontology: &OntologyRegistry,
    fn_name: &str,
    fn_params: &[Param],
    specs: Vec<(ObligationKind, Vec<Param>, Expr)>,
    include_axioms: bool,
    proved_lemmas: &[ProofDecl],
    run_smt: bool,
) -> Vec<ProofObligation> {
    if !run_smt || specs.len() <= 1 {
        return specs
            .into_iter()
            .map(|(kind, state_params, vc)| {
                build_vc_obligation(
                    program,
                    ontology,
                    fn_name,
                    kind,
                    fn_params,
                    &state_params,
                    &vc,
                    include_axioms,
                    proved_lemmas,
                    run_smt,
                )
            })
            .collect();
    }

    let mut union_params = Vec::new();
    let mut seen = BTreeSet::new();
    for p in fn_params {
        if seen.insert(p.name.clone()) {
            union_params.push(p.clone());
        }
    }
    for (_, sp, _) in &specs {
        for p in sp {
            if seen.insert(p.name.clone()) {
                union_params.push(p.clone());
            }
        }
    }

    let header_opt = emit_vc_smt2_header(
        program,
        ontology,
        &union_params,
        include_axioms,
        proved_lemmas,
    );
    let refutations_opt: Option<Vec<String>> = specs
        .iter()
        .map(|(_, _, vc)| vc_to_smt(program, ontology, vc).map(|s| format!("(not {})", s)))
        .collect();

    let batch_smt = match (header_opt, refutations_opt) {
        (Some(header), Some(refutations)) => {
            run_smt_incremental_batch_with_prover(Prover::Auto, &header, &refutations)
        }
        _ => None,
    };

    let Some((prover_name, verdicts)) = batch_smt else {
        return specs
            .into_iter()
            .map(|(kind, state_params, vc)| {
                build_vc_obligation(
                    program,
                    ontology,
                    fn_name,
                    kind,
                    fn_params,
                    &state_params,
                    &vc,
                    include_axioms,
                    proved_lemmas,
                    run_smt,
                )
            })
            .collect();
    };

    specs
        .into_iter()
        .zip(verdicts)
        .map(|((kind, state_params, vc), verdict)| {
            let (bounded_ok, ce, samples) =
                check_vc_bounded(program, ontology, fn_params, &state_params, &vc);

            let mut all_params = Vec::new();
            let mut p_seen = BTreeSet::new();
            for p in fn_params.iter().chain(state_params.iter()) {
                if p_seen.insert(p.name.clone()) {
                    all_params.push(p.clone());
                }
            }

            let smt2_script = emit_vc_smt2(
                program,
                ontology,
                &all_params,
                &vc,
                include_axioms,
                proved_lemmas,
            );
            let smt_res = ProverResult {
                prover: prover_name.clone(),
                verdict,
                stdout: match verdict {
                    Verdict::Consistent => "sat".into(),
                    Verdict::Inconsistent => "unsat".into(),
                    _ => "unknown".into(),
                },
                stderr: String::new(),
                elapsed_ms: 0,
                detail: format!("{} incremental batch ({})", prover_name, verdict),
            };
            let smt_res = match &smt2_script {
                Some(script) => attach_model(smt_res, script),
                None => smt_res,
            };
            let agr = evaluate_vc_agreement(bounded_ok, smt_res.verdict);
            let status = decide_status_sampled(ce.clone(), samples, Some(&smt_res));
            let verified = matches!(status, Status::Proved { .. } | Status::BoundedOnly { .. });
            let counterexample = match &status {
                Status::Refuted { counterexample } => Some(counterexample.clone()),
                _ => ce,
            };

            ProofObligation {
                fn_name: fn_name.to_string(),
                kind,
                formula_desc: format_expr_concise(&vc),
                status,
                verified,
                counterexample,
                smt_prover: Some(smt_res.prover),
                smt_verdict: Some(smt_res.verdict),
                agreement: Some(agr),
                smt2_script,
            }
        })
        .collect()
}

/// Generates all Dijkstra Weakest Precondition (`wp`), Refinement (`refines`),
/// and Verus Ghost Proof (`proof`) obligations purely in-memory without spawning external SMT solvers.
pub fn generate_obligations(
    program: &Program,
    ontology: &OntologyRegistry,
) -> Vec<ProofObligation> {
    verify_program_inner(program, ontology, false)
}

/// Generates and verifies all Dijkstra Weakest Precondition (`wp`), Refinement (`refines`),
/// and Verus Ghost Proof (`proof`) obligations using both bounded domain search and unbounded SMT-LIB2.
pub fn verify_program(program: &Program, ontology: &OntologyRegistry) -> Vec<ProofObligation> {
    verify_program_inner(program, ontology, true)
}

fn verify_program_inner(
    program: &Program,
    ontology: &OntologyRegistry,
    run_smt: bool,
) -> Vec<ProofObligation> {
    let mut obligations = Vec::new();
    let mut specs = BTreeMap::new();
    for item in &program.items {
        if let Item::Spec(sp) = item {
            specs.insert(sp.name.clone(), sp.clone());
        }
    }

    let has_axioms = program.items.iter().any(|i| matches!(i, Item::Axiom(_)));
    let axioms_consistent = if run_smt && has_axioms {
        let consistency = crate::smt::check_ontology_consistency(program, ontology, Prover::Auto);
        consistency.verdict != Verdict::Inconsistent
    } else {
        true
    };
    let mut proved_lemmas: Vec<ProofDecl> = Vec::new();

    for item in &program.items {
        match item {
            Item::Proof(pr) => {
                let req = pr.requires.clone().unwrap_or(Expr::Bool(true));
                let body = pr.body.clone().unwrap_or(Expr::Bool(true));
                let ens = pr.ensures.clone();
                let vc = implies(conj(req, body), ens);
                let ob = build_vc_obligation(
                    program,
                    ontology,
                    &pr.name,
                    ObligationKind::ProofLemma,
                    &pr.params,
                    &[],
                    &vc,
                    axioms_consistent,
                    &proved_lemmas,
                    run_smt,
                );
                if matches!(ob.status, Status::Proved { .. }) {
                    proved_lemmas.push(pr.clone());
                }
                obligations.push(ob);
            }
            Item::FnDecl(f) => {
                let pre = f.requires.clone().unwrap_or(Expr::Bool(true));
                let post = f.ensures.clone().unwrap_or(Expr::Bool(true));

                // 1. Refinement Calculus Obligations (`fn` refines `spec`)
                if let Some(spec_name) = &f.refines {
                    if let Some(spec) = specs.get(spec_name) {
                        let mut param_map = BTreeMap::new();
                        for (sp_p, fn_p) in spec.params.iter().zip(f.params.iter()) {
                            param_map.insert(sp_p.name.clone(), Expr::Var(fn_p.name.clone()));
                        }
                        let spec_pre = spec
                            .requires
                            .as_ref()
                            .map(|r| subst_expr(r, &param_map))
                            .unwrap_or(Expr::Bool(true));
                        let spec_ens = spec
                            .ensures
                            .as_ref()
                            .map(|e| subst_expr(e, &param_map))
                            .unwrap_or(Expr::Bool(true));

                        // Pre_spec => Pre_impl
                        let vc_pre = implies(spec_pre, pre.clone());
                        obligations.push(build_vc_obligation(
                            program,
                            ontology,
                            &f.name,
                            ObligationKind::RefinementPrecondition(spec_name.clone()),
                            &f.params,
                            &[],
                            &vc_pre,
                            false,
                            &proved_lemmas,
                            run_smt,
                        ));

                        // (Pre_spec && Post_impl) => Post_spec (checked over actual execution of f + SMT on contract)
                        let (ok_post, ce_post, samples_post) =
                            check_refinement_execution(program, ontology, f, &spec_ens);
                        let mut post_params = f.params.clone();
                        post_params.push(Param {
                            name: "result".into(),
                            ty: f.ret_ty.clone(),
                        });
                        let vc_post_formula = implies(conj(pre.clone(), post.clone()), spec_ens.clone());
                        let smt2_script = emit_vc_smt2(
                            program,
                            ontology,
                            &post_params,
                            &vc_post_formula,
                            false,
                            &proved_lemmas,
                        );
                        let smt_res = if run_smt {
                            smt2_script
                                .as_ref()
                                .map(|script| {
                                    attach_model(run_smt_prover(Prover::Auto, script), script)
                                })
                        } else {
                            None
                        };
                        let (smt_prover, smt_verdict, agreement) =
                            if let Some(ref res) = smt_res {
                                let agr = evaluate_vc_agreement(ok_post, res.verdict);
                                (Some(res.prover.clone()), Some(res.verdict), Some(agr))
                            } else {
                                (None, None, None)
                            };
                        let status = decide_status_sampled(ce_post.clone(), samples_post, smt_res.as_ref());
                        let verified =
                            matches!(status, Status::Proved { .. } | Status::BoundedOnly { .. });
                        let counterexample = match &status {
                            Status::Refuted { counterexample } => Some(counterexample.clone()),
                            _ => ce_post,
                        };
                        obligations.push(ProofObligation {
                            fn_name: f.name.clone(),
                            kind: ObligationKind::RefinementPostcondition(spec_name.clone()),
                            formula_desc: format!(
                                "({} && {}) => {}",
                                format_expr_concise(&pre),
                                format_expr_concise(&post),
                                format_expr_concise(&spec_ens)
                            ),
                            status,
                            verified,
                            counterexample,
                            smt_prover,
                            smt_verdict,
                            agreement,
                            smt2_script,
                        });
                    }
                }

                // 2. Structural GCL obligations inside function body (peeling outer let-bindings)
                let peeled_body = peel_let_bindings(&f.body);
                match &peeled_body {
                    Expr::IfFi { branches } => {
                        let mut batch_specs = Vec::with_capacity(1 + branches.len());
                        // Obligation A: Guard Totality: Pre => (G1 ∨ G2 ∨ ... ∨ Gn)
                        let bb = branches
                            .iter()
                            .map(|b| b.guard.clone())
                            .fold(Expr::Bool(false), disj);
                        let vc_totality = implies(pre.clone(), bb);
                        batch_specs.push((ObligationKind::IfFiGuardTotality, Vec::new(), vc_totality));

                        // Obligation B: Each branch satisfies Post: (Pre ∧ Gi) => wp(Si, Post)
                        for (idx, br) in branches.iter().enumerate() {
                            let wp_s = wp_branch_body(&br.body, &post, None);
                            let vc_br = implies(conj(pre.clone(), br.guard.clone()), wp_s);
                            batch_specs.push((
                                ObligationKind::IfFiBranchPostcondition(idx),
                                Vec::new(),
                                vc_br,
                            ));
                        }
                        obligations.extend(build_vc_obligations_batch(
                            program,
                            ontology,
                            &f.name,
                            &f.params,
                            batch_specs,
                            false,
                            &proved_lemmas,
                            run_smt,
                        ));
                    }
                    Expr::DoOd {
                        inits,
                        invariant,
                        variant,
                        branches,
                        then_expr,
                    } => {
                        let inv = invariant
                            .as_ref()
                            .map(|b| (**b).clone())
                            .unwrap_or(Expr::Bool(true));

                        let mut init_map = BTreeMap::new();
                        let mut state_params = Vec::new();
                        for (vname, iexpr) in inits {
                            init_map.insert(vname.clone(), iexpr.clone());
                            let sty = f
                                .params
                                .iter()
                                .find(|p| Expr::Var(p.name.clone()) == *iexpr)
                                .map(|p| p.ty.clone())
                                .unwrap_or(TypeExpr::Named("Int".into()));
                            state_params.push(Param {
                                name: vname.clone(),
                                ty: sty,
                            });
                        }

                        let mut batch_specs = Vec::new();

                        // 1. Initialization: Pre => I[state := init]
                        let inv_init = subst_expr(&inv, &init_map);
                        let vc_init = implies(pre.clone(), inv_init);
                        batch_specs.push((ObligationKind::DoOdInitialization, Vec::new(), vc_init));

                        let default_state_var = inits.first().map(|(n, _)| n.as_str());

                        // 2. Preservation & 3/4. Variant obligations per branch
                        for (idx, br) in branches.iter().enumerate() {
                            let pre_inv_g = conj(pre.clone(), conj(inv.clone(), br.guard.clone()));
                            let wp_inv = wp_branch_body(&br.body, &inv, default_state_var);
                            let vc_pres = implies(pre_inv_g.clone(), wp_inv);
                            batch_specs.push((
                                ObligationKind::DoOdPreservation(idx),
                                state_params.clone(),
                                vc_pres,
                            ));

                            if let Some(var_expr) = variant {
                                // Non-negativity: (Pre ∧ I ∧ Gi) => V >= 0
                                let v_non_neg = Expr::Binary {
                                    op: BinOp::Ge,
                                    left: var_expr.clone(),
                                    right: Box::new(Expr::Int(0)),
                                };
                                let vc_nn = implies(pre_inv_g.clone(), v_non_neg);
                                batch_specs.push((
                                    ObligationKind::DoOdVariantNonNegative(idx),
                                    state_params.clone(),
                                    vc_nn,
                                ));

                                // Strict decrease: (Pre ∧ I ∧ Gi) => wp(Si, V) < V
                                let wp_v = wp_branch_body(&br.body, var_expr, default_state_var);
                                let v_dec = Expr::Binary {
                                    op: BinOp::Lt,
                                    left: Box::new(wp_v),
                                    right: var_expr.clone(),
                                };
                                let vc_dec = implies(pre_inv_g, v_dec);
                                batch_specs.push((
                                    ObligationKind::DoOdVariantDecrease(idx),
                                    state_params.clone(),
                                    vc_dec,
                                ));
                            }
                        }

                        // 5. Exit Postcondition: (Pre ∧ I ∧ ¬BB) => Post[result := then_expr]
                        let bb = branches
                            .iter()
                            .map(|b| b.guard.clone())
                            .fold(Expr::Bool(false), disj);
                        let mut res_map = BTreeMap::new();
                        res_map.insert("result".into(), (**then_expr).clone());
                        let post_exit = subst_expr(&post, &res_map);
                        let vc_exit = implies(conj(pre.clone(), conj(inv, not(bb))), post_exit);
                        batch_specs.push((
                            ObligationKind::DoOdExitPostcondition,
                            state_params,
                            vc_exit,
                        ));

                        obligations.extend(build_vc_obligations_batch(
                            program,
                            ontology,
                            &f.name,
                            &f.params,
                            batch_specs,
                            false,
                            &proved_lemmas,
                            run_smt,
                        ));
                    }
                    _ => {
                        if f.requires.is_some() || f.ensures.is_some() {
                            let (ok, ce, samples) =
                                check_refinement_execution(program, ontology, f, &post);
                            let mut map = BTreeMap::new();
                            map.insert("result".to_string(), f.body.clone());
                            let vc_direct = implies(pre.clone(), subst_expr(&post, &map));
                            let smt2_script = emit_vc_smt2(
                                program,
                                ontology,
                                &f.params,
                                &vc_direct,
                                axioms_consistent,
                                &proved_lemmas,
                            );
                            let smt_res = if run_smt {
                                smt2_script
                                    .as_ref()
                                    .map(|script| {
                                    attach_model(run_smt_prover(Prover::Auto, script), script)
                                })
                            } else {
                                None
                            };
                            let (smt_prover, smt_verdict, agreement) =
                                if let Some(ref res) = smt_res {
                                    let agr = evaluate_vc_agreement(ok, res.verdict);
                                    (Some(res.prover.clone()), Some(res.verdict), Some(agr))
                                } else {
                                    (None, None, None)
                                };
                            let status = decide_status_sampled(ce.clone(), samples, smt_res.as_ref());
                            let verified = matches!(
                                status,
                                Status::Proved { .. } | Status::BoundedOnly { .. }
                            );
                            let counterexample = match &status {
                                Status::Refuted { counterexample } => Some(counterexample.clone()),
                                _ => ce,
                            };
                            obligations.push(ProofObligation {
                                fn_name: f.name.clone(),
                                kind: ObligationKind::FunctionContract,
                                formula_desc: format!(
                                    "{} => wp(body, {})",
                                    format_expr_concise(&pre),
                                    format_expr_concise(&post)
                                ),
                                status,
                                verified,
                                counterexample,
                                smt_prover,
                                smt_verdict,
                                agreement,
                                smt2_script,
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }

    obligations
}

/// Most parameter assignments the bounded cross-check evaluates for one obligation. Spaces up to
/// this size are enumerated exhaustively; larger ones get a deterministic sample of this size.
pub const SAMPLE_BUDGET: usize = 10_000;

/// How many assignments a bounded check evaluated, out of how many its sample domains span.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Samples {
    pub evaluated: usize,
    pub space: usize,
}

/// Chooses which assignments (one index per domain) to evaluate. When the product of `sizes` fits
/// `budget`, every assignment is returned in lexicographic order. Otherwise the result starts with
/// a pairwise covering array, so every pair of values of every two domains appears together, when
/// one fits the budget, or else with assignments that together use every value of every domain.
/// Distinct fixed-seed pseudo-random assignments fill the rest of the budget.
fn plan_samples(sizes: &[usize], budget: usize) -> (Vec<Vec<usize>>, usize) {
    let space = sizes.iter().fold(1usize, |acc, &n| acc.saturating_mul(n));
    if space == 0 {
        return (Vec::new(), 0);
    }
    if space <= budget {
        let mut plan = Vec::with_capacity(space);
        let mut idx = vec![0usize; sizes.len()];
        loop {
            plan.push(idx.clone());
            let mut d = sizes.len();
            loop {
                if d == 0 {
                    return (plan, space);
                }
                d -= 1;
                idx[d] += 1;
                if idx[d] < sizes[d] {
                    break;
                }
                idx[d] = 0;
            }
        }
    }

    let mut seen = BTreeSet::new();
    let mut plan = Vec::with_capacity(budget);
    let first = pairwise_rows(sizes, budget).unwrap_or_else(|| {
        let widest = sizes.iter().copied().max().unwrap_or(0);
        (0..widest.min(budget))
            .map(|i| sizes.iter().map(|&n| i % n).collect())
            .collect()
    });
    for a in first.into_iter().take(budget) {
        if seen.insert(a.clone()) {
            plan.push(a);
        }
    }
    // xorshift64*, fixed seed: the same program always gets the same samples.
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut attempts = 0;
    while plan.len() < budget && attempts < budget * 8 {
        attempts += 1;
        let a: Vec<usize> = sizes
            .iter()
            .map(|&n| {
                state ^= state >> 12;
                state ^= state << 25;
                state ^= state >> 27;
                (state.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 33) as usize % n
            })
            .collect();
        if seen.insert(a.clone()) {
            plan.push(a);
        }
    }
    (plan, space)
}

/// A pairwise covering array over domains of `sizes`, built with the deterministic IPOG strategy
/// (Lei and Tai): cover all pairs of the two largest domains, then add one domain at a time, first
/// extending each row with the value that covers the most new pairs, then adding rows for the pairs
/// still missing. `None` when the two largest domains alone need more than `budget` rows.
fn pairwise_rows(sizes: &[usize], budget: usize) -> Option<Vec<Vec<usize>>> {
    let mut order: Vec<usize> = (0..sizes.len()).collect();
    order.sort_by_key(|&d| std::cmp::Reverse(sizes[d]));
    let s: Vec<usize> = order.iter().map(|&d| sizes[d]).collect();
    if s.len() < 2 || s[0].checked_mul(s[1])? > budget {
        return None;
    }
    let k = s.len();
    let mut rows: Vec<Vec<Option<usize>>> = Vec::with_capacity(s[0] * s[1]);
    for a in 0..s[0] {
        for b in 0..s[1] {
            let mut row = vec![None; k];
            row[0] = Some(a);
            row[1] = Some(b);
            rows.push(row);
        }
    }
    for p in 2..k {
        let np = s[p];
        // uncovered[j][a * np + b]: value `a` of domain `j` has not yet met value `b` of domain `p`.
        let mut uncovered: Vec<Vec<bool>> = (0..p).map(|j| vec![true; s[j] * np]).collect();
        for (r, row) in rows.iter_mut().enumerate() {
            let gain = |b: usize| {
                (0..p)
                    .filter(|&j| row[j].is_some_and(|a| uncovered[j][a * np + b]))
                    .count()
            };
            // Ties go to the first value at or after this row's position, which spreads values
            // across rows.
            let best = (0..np)
                .max_by_key(|&b| (gain(b), std::cmp::Reverse((b + np - r % np) % np)))
                .unwrap_or(0);
            row[p] = Some(best);
            for j in 0..p {
                if let Some(a) = row[j] {
                    uncovered[j][a * np + best] = false;
                }
            }
        }
        for j in 0..p {
            for a in 0..s[j] {
                for b in 0..np {
                    if !uncovered[j][a * np + b] {
                        continue;
                    }
                    match rows
                        .iter_mut()
                        .find(|row| row[p] == Some(b) && row[j].is_none())
                    {
                        Some(row) => row[j] = Some(a),
                        None => {
                            if rows.len() >= budget {
                                return None;
                            }
                            let mut row = vec![None; k];
                            row[j] = Some(a);
                            row[p] = Some(b);
                            rows.push(row);
                        }
                    }
                    uncovered[j][a * np + b] = false;
                }
            }
        }
    }
    // Unconstrained positions take a value that varies by row, then domains go back in input order.
    Some(
        rows.iter()
            .enumerate()
            .map(|(r, row)| {
                let mut out = vec![0; k];
                for (i, &d) in order.iter().enumerate() {
                    out[d] = row[i].unwrap_or(r % s[i]);
                }
                out
            })
            .collect(),
    )
}

/// Evaluates `check` on each planned assignment of `domains` until it reports a counterexample.
fn search_samples(
    domains: &[(String, Vec<Value>)],
    mut check: impl FnMut(&BTreeMap<String, Value>) -> Sample,
) -> (bool, Option<String>, Samples) {
    let sizes: Vec<usize> = domains.iter().map(|(_, vals)| vals.len()).collect();
    let (plan, space) = plan_samples(&sizes, SAMPLE_BUDGET);
    let mut samples = Samples {
        evaluated: 0,
        space,
    };
    let mut env = BTreeMap::new();
    for assignment in &plan {
        for ((name, vals), &i) in domains.iter().zip(assignment) {
            env.insert(name.clone(), vals[i].clone());
        }
        match check(&env) {
            Sample::Pass => samples.evaluated += 1,
            Sample::Skip => {}
            Sample::Fail(ce) => {
                samples.evaluated += 1;
                return (false, Some(ce), samples);
            }
        }
    }
    (true, None, samples)
}

/// Outcome of evaluating one sampled assignment.
enum Sample {
    Pass,
    Fail(String),
    /// The interpreter ran out of call depth, which says nothing about the obligation.
    Skip,
}

impl Sample {
    fn from_error(env: &BTreeMap<String, Value>, e: &crate::eval::RuntimeError) -> Sample {
        if e.message.starts_with(crate::eval::CALL_DEPTH_EXCEEDED) {
            Sample::Skip
        } else {
            Sample::Fail(format!("{} -> {}", format_env_assignment(env), e))
        }
    }
}

/// Loads the program's types, functions and specs into a fresh interpreter for bounded checks.
fn bounded_interpreter(program: &Program, ontology: &OntologyRegistry) -> Interpreter {
    let mut interp = Interpreter::new(ontology.clone(), 42, false);
    let _ = interp.run_program(&Program {
        expr_spans: Vec::new(),
        items: program
            .items
            .iter()
            .filter(|i| matches!(i, Item::TypeDecl(_) | Item::FnDecl(_) | Item::Spec(_)))
            .cloned()
            .collect(),
    });
    interp
}

/// Bounded domain search for a Verification Condition
fn check_vc_bounded(
    program: &Program,
    ontology: &OntologyRegistry,
    fn_params: &[Param],
    state_params: &[Param],
    vc: &Expr,
) -> (bool, Option<String>, Samples) {
    let mut all_params = Vec::new();
    let mut seen = BTreeSet::new();
    for p in fn_params.iter().chain(state_params.iter()) {
        if seen.insert(p.name.clone()) {
            all_params.push(p.clone());
        }
    }

    let mut extra_ints = BTreeSet::new();
    extract_int_constants(vc, &mut extra_ints);

    let domains: Vec<(String, Vec<Value>)> = all_params
        .iter()
        .map(|p| {
            (
                p.name.clone(),
                sample_domain_for_type(&p.ty, ontology, program, &extra_ints),
            )
        })
        .collect();

    let mut interp = bounded_interpreter(program, ontology);
    search_samples(&domains, |env| match interp.eval_expr(vc, env) {
        Ok(Value::Bool(true)) => Sample::Pass,
        Ok(Value::Bool(false)) => Sample::Fail(format_env_assignment(env)),
        Ok(other) => Sample::Fail(format!(
            "{} -> non-boolean VC: {}",
            format_env_assignment(env),
            other
        )),
        Err(e) => Sample::from_error(env, &e),
    })
}

fn check_refinement_execution(
    program: &Program,
    ontology: &OntologyRegistry,
    f: &FnDecl,
    post: &Expr,
) -> (bool, Option<String>, Samples) {
    let mut extra_ints = BTreeSet::new();
    if let Some(req) = &f.requires {
        extract_int_constants(req, &mut extra_ints);
    }
    extract_int_constants(&f.body, &mut extra_ints);
    extract_int_constants(post, &mut extra_ints);

    let domains: Vec<(String, Vec<Value>)> = f
        .params
        .iter()
        .map(|p| {
            (
                p.name.clone(),
                sample_domain_for_type(&p.ty, ontology, program, &extra_ints),
            )
        })
        .collect();

    let mut interp = bounded_interpreter(program, ontology);
    let pre = f.requires.clone().unwrap_or(Expr::Bool(true));
    search_samples(&domains, |env| {
        if interp.eval_expr(&pre, env).unwrap_or(Value::Bool(false)) != Value::Bool(true) {
            return Sample::Pass;
        }
        match interp.eval_expr(&f.body, env) {
            Ok(res) => {
                let mut post_env = env.clone();
                post_env.insert("result".into(), res);
                match interp.eval_expr(post, &post_env) {
                    Ok(Value::Bool(true)) => Sample::Pass,
                    Err(e) => Sample::from_error(&post_env, &e),
                    _ => Sample::Fail(format_env_assignment(&post_env)),
                }
            }
            Err(e) => Sample::from_error(env, &e),
        }
    })
}

fn format_env_assignment(env: &BTreeMap<String, Value>) -> String {
    let parts: Vec<String> = env.iter().map(|(k, v)| format!("{} = {}", k, v)).collect();
    format!("{{ {} }}", parts.join(", "))
}

fn sample_domain_for_type(
    ty: &TypeExpr,
    ontology: &OntologyRegistry,
    program: &Program,
    extra_ints: &BTreeSet<i64>,
) -> Vec<Value> {
    use std::rc::Rc;

    match ty {
        TypeExpr::Named(n) => match n.as_str() {
            "Int" | "Integer" => {
                let mut set: BTreeSet<i64> = [-1, 0, 1, 2, 6, 12, 800, 950, 1250]
                    .into_iter()
                    .collect();
                for &c in extra_ints {
                    if set.len() < 16 {
                        set.insert(c);
                    }
                }
                set.into_iter().map(Value::Int).collect()
            }
            "Float" | "Double" => vec![Value::Float(-1.0), Value::Float(0.0), Value::Float(1.0)],
            "Bool" | "Boolean" => vec![Value::Bool(false), Value::Bool(true)],
            "String" | "Str" => vec![Value::Str(String::new()), Value::Str("id-1".into())],
            other => {
                if let Some(cinfo) = ontology.concepts.get(other) {
                    let mut int_samples: Vec<i64> = vec![-50, 0, 500, 800, 950, 1300];
                    for &c in extra_ints.iter().take(4) {
                        if !int_samples.contains(&c) {
                            int_samples.push(c);
                        }
                    }
                    let mut instances = Vec::new();
                    for (idx, &p) in int_samples.iter().enumerate() {
                        let alt_p = int_samples[(idx + 1) % int_samples.len()];
                        for skew in [false, true] {
                            let mut fmap = BTreeMap::new();
                            for (f_idx, (fname, fty)) in cinfo.all_fields.iter().enumerate() {
                                let chosen_int = if skew && f_idx % 2 == 1 { alt_p } else { p };
                                let fval = match fty {
                                    TypeExpr::Named(tn) if tn == "Int" || tn == "Integer" => {
                                        Value::Int(chosen_int)
                                    }
                                    TypeExpr::Named(tn) if tn == "Bool" || tn == "Boolean" => {
                                        Value::Bool(!skew)
                                    }
                                    TypeExpr::Named(tn) if tn == "String" || tn == "Str" => {
                                        Value::Str("P-1".into())
                                    }
                                    _ => Value::Int(0),
                                };
                                fmap.insert(fname.clone(), fval);
                            }
                            let inst = Value::ConceptInstance {
                                concept: other.to_string(),
                                fields: fmap,
                            };
                            if !instances.contains(&inst) {
                                instances.push(inst);
                            }
                        }
                    }
                    instances
                } else {
                    for item in &program.items {
                        if let Item::TypeDecl(adt) = item {
                            if adt.name == other {
                                let mut variants = Vec::new();
                                for v in &adt.variants {
                                    let fields: Vec<Value> = v
                                        .payload
                                        .iter()
                                        .map(|pty| {
                                            sample_domain_for_type(
                                                pty,
                                                ontology,
                                                program,
                                                extra_ints,
                                            )
                                            .into_iter()
                                            .next()
                                            .unwrap_or(Value::Unit)
                                        })
                                        .collect();
                                    variants.push(Value::AdtVariant {
                                        variant: v.name.clone(),
                                        fields,
                                    });
                                }
                                if !variants.is_empty() {
                                    return variants;
                                }
                            }
                        }
                    }
                    vec![Value::Unit]
                }
            }
        },
        TypeExpr::List(inner) => {
            let elem_samples = sample_domain_for_type(inner, ontology, program, extra_ints);
            let mut lists = vec![Value::List(Rc::new(vec![]))];
            if let Some(first) = elem_samples.first() {
                lists.push(Value::List(Rc::new(vec![first.clone()])));
            }
            if elem_samples.len() >= 2 {
                lists.push(Value::List(Rc::new(vec![
                    elem_samples[0].clone(),
                    elem_samples[1].clone(),
                ])));
            }
            lists
        }
        _ => vec![Value::Unit],
    }
}

#[cfg(test)]
mod sample_plan_tests {
    use super::*;

    #[test]
    fn small_spaces_are_enumerated_in_lexicographic_order() {
        let (plan, space) = plan_samples(&[2, 3], 100);
        assert_eq!(space, 6);
        assert_eq!(
            plan,
            vec![
                vec![0, 0],
                vec![0, 1],
                vec![0, 2],
                vec![1, 0],
                vec![1, 1],
                vec![1, 2]
            ]
        );
        assert_eq!(plan_samples(&[], 100), (vec![vec![]], 1));
        assert_eq!(plan_samples(&[3, 0], 100), (vec![], 0));
    }

    #[test]
    fn large_spaces_are_sampled_within_budget_and_cover_every_value() {
        let sizes = [16, 3, 16, 16, 16, 9];
        let (plan, space) = plan_samples(&sizes, 500);
        assert_eq!(space, 16 * 3 * 16 * 16 * 16 * 9);
        assert_eq!(plan.len(), 500);
        let distinct: BTreeSet<_> = plan.iter().collect();
        assert_eq!(distinct.len(), 500, "samples are distinct");
        for (d, &n) in sizes.iter().enumerate() {
            let used: BTreeSet<usize> = plan.iter().map(|a| a[d]).collect();
            assert_eq!(used.len(), n, "every value of domain {d} is tried");
        }
        assert_eq!(plan_samples(&sizes, 500).0, plan, "sampling is deterministic");
    }

    #[test]
    fn sampled_plans_cover_every_pair_of_values() {
        let sizes = [5, 12, 3, 9, 7, 12, 4];
        let (plan, space) = plan_samples(&sizes, 2_000);
        assert!(space > 2_000);
        for d in 0..sizes.len() {
            for e in d + 1..sizes.len() {
                let pairs: BTreeSet<(usize, usize)> = plan.iter().map(|a| (a[d], a[e])).collect();
                assert_eq!(pairs.len(), sizes[d] * sizes[e], "domains {d} and {e}");
            }
        }
        let rows = pairwise_rows(&sizes, 2_000).unwrap();
        assert!(rows.len() < 300, "covering array stays small: {}", rows.len());
        assert!(pairwise_rows(&[20; 12], SAMPLE_BUDGET).unwrap().len() < 1_000);
        // When the two largest domains alone exceed the budget, pairwise coverage is not attempted.
        assert_eq!(pairwise_rows(&[200, 100, 3], 10_000), None);
    }

    #[test]
    fn huge_spaces_saturate_instead_of_overflowing() {
        let (plan, space) = plan_samples(&[1 << 20; 8], 10);
        assert_eq!(space, usize::MAX);
        assert_eq!(plan.len(), 10);
    }
}
