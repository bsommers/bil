use crate::ast::*;
use crate::eval::{Interpreter, Value};
use crate::ontology::OntologyRegistry;
use crate::smt::{
    emit_vc_smt2, evaluate_vc_agreement, run_smt_prover, AgreementOutcome, Prover, ProverResult,
    Verdict,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    Proved { by: String },
    Refuted { counterexample: String },
    BoundedOnly { samples: usize },
    Unknown { reason: String },
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Status::Proved { by } => write!(f, "PROVED (by {})", by),
            Status::Refuted { .. } => write!(f, "REFUTED"),
            Status::BoundedOnly { samples } => write!(f, "BOUNDED ({} samples)", samples),
            Status::Unknown { reason } => write!(f, "UNKNOWN ({})", reason),
        }
    }
}

pub fn decide_status(
    bounded_ce: Option<String>,
    samples: usize,
    smt: Option<&ProverResult>,
) -> Status {
    if let Some(ce) = bounded_ce {
        return Status::Refuted { counterexample: ce };
    }
    match smt.map(|r| (&r.verdict, r.prover.as_str(), r.stdout.as_str(), r.detail.as_str())) {
        Some((Verdict::Inconsistent, prover, _, _)) => Status::Proved {
            by: prover.to_string(),
        },
        Some((Verdict::Consistent, _, stdout, _)) => Status::Refuted {
            counterexample: format!("SMT model: {}", stdout.trim()),
        },
        Some((Verdict::Skipped, _, _, _)) | Some((Verdict::Unknown, _, _, _)) | None
            if samples > 0 =>
        {
            Status::BoundedOnly { samples }
        }
        Some((_, _, _, detail)) => Status::Unknown {
            reason: detail.to_string(),
        },
        None => Status::Unknown {
            reason: "no solver and no samples".into(),
        },
    }
}

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone)]
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

/// Collects all free variable names occurring in `expr`.
pub fn free_vars(expr: &Expr) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    collect_free_vars(expr, &BTreeSet::new(), &mut vars);
    vars
}

fn collect_free_vars(expr: &Expr, bound: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    match expr {
        Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Placeholder => {}
        Expr::Var(name) => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        Expr::Unary { expr: inner, .. } => collect_free_vars(inner, bound, out),
        Expr::Binary { left, right, .. } => {
            collect_free_vars(left, bound, out);
            collect_free_vars(right, bound, out);
        }
        Expr::Quantifier {
            var, domain, body, ..
        } => {
            collect_free_vars(domain, bound, out);
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_free_vars(body, &inner_bound, out);
        }
        Expr::IfFi { branches } => {
            for br in branches {
                collect_free_vars(&br.guard, bound, out);
                match &br.body {
                    GclBody::Expr(e) => collect_free_vars(e, bound, out),
                    GclBody::Updates(ups) => {
                        for (_, ue) in ups {
                            collect_free_vars(ue, bound, out);
                        }
                    }
                    GclBody::Skip | GclBody::Abort => {}
                }
            }
        }
        Expr::DoOd {
            inits,
            invariant,
            variant,
            branches,
            then_expr,
        } => {
            let mut inner_bound = bound.clone();
            for (vname, iexpr) in inits {
                collect_free_vars(iexpr, &inner_bound, out);
                inner_bound.insert(vname.clone());
            }
            if let Some(inv) = invariant {
                collect_free_vars(inv, &inner_bound, out);
            }
            if let Some(var_e) = variant {
                collect_free_vars(var_e, &inner_bound, out);
            }
            for br in branches {
                collect_free_vars(&br.guard, &inner_bound, out);
                match &br.body {
                    GclBody::Expr(e) => collect_free_vars(e, &inner_bound, out),
                    GclBody::Updates(ups) => {
                        for (_, ue) in ups {
                            collect_free_vars(ue, &inner_bound, out);
                        }
                    }
                    GclBody::Skip | GclBody::Abort => {}
                }
            }
            collect_free_vars(then_expr, &inner_bound, out);
        }
        Expr::Match { scrutinee, arms } => {
            collect_free_vars(scrutinee, bound, out);
            for arm in arms {
                let mut arm_bound = bound.clone();
                for pv in pattern_bound_vars(&arm.pattern) {
                    arm_bound.insert(pv);
                }
                collect_free_vars(&arm.body, &arm_bound, out);
            }
        }
        Expr::RecordInit { fields, .. } => {
            for (_, v) in fields {
                collect_free_vars(v, bound, out);
            }
        }
        Expr::RecordWith { base, updates } => {
            collect_free_vars(base, bound, out);
            for (_, v) in updates {
                collect_free_vars(v, bound, out);
            }
        }
        Expr::FieldAccess { base, .. } => collect_free_vars(base, bound, out),
        Expr::Call { args, .. } => {
            for a in args {
                collect_free_vars(a, bound, out);
            }
        }
        Expr::List(items) => {
            for i in items {
                collect_free_vars(i, bound, out);
            }
        }
        Expr::LetIn { name, value, body } => {
            collect_free_vars(value, bound, out);
            let mut inner_bound = bound.clone();
            inner_bound.insert(name.clone());
            collect_free_vars(body, &inner_bound, out);
        }
    }
}

fn pattern_bound_vars(pat: &Pattern) -> Vec<String> {
    match pat {
        Pattern::Var(v) if v != "_" => vec![v.clone()],
        Pattern::Variant(_, bindings) => bindings
            .iter()
            .filter(|b| b.as_str() != "_")
            .cloned()
            .collect(),
        _ => Vec::new(),
    }
}

fn fresh_var_name(base: &str, avoid: &BTreeSet<String>) -> String {
    let mut idx = 0usize;
    loop {
        let candidate = format!("{}_{}", base, idx);
        if !avoid.contains(&candidate) {
            return candidate;
        }
        idx += 1;
    }
}

fn subst_gcl_branch(br: &GuardedBranch, mapping: &BTreeMap<String, Expr>) -> GuardedBranch {
    GuardedBranch {
        guard: subst_expr(&br.guard, mapping),
        body: match &br.body {
            GclBody::Expr(e) => GclBody::Expr(subst_expr(e, mapping)),
            GclBody::Updates(ups) => GclBody::Updates(
                ups.iter()
                    .map(|(v, ue)| (v.clone(), subst_expr(ue, mapping)))
                    .collect(),
            ),
            other => other.clone(),
        },
    }
}

/// Capture-avoiding simultaneous substitution `expr[var := replacement]` (Dijkstra's textual substitution)
pub fn subst_expr(expr: &Expr, mapping: &BTreeMap<String, Expr>) -> Expr {
    if mapping.is_empty() {
        return expr.clone();
    }
    match expr {
        Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Placeholder => {
            expr.clone()
        }
        Expr::Var(name) => mapping.get(name).cloned().unwrap_or_else(|| expr.clone()),
        Expr::Unary { op, expr: inner } => Expr::Unary {
            op: *op,
            expr: Box::new(subst_expr(inner, mapping)),
        },
        Expr::Binary { op, left, right } => Expr::Binary {
            op: *op,
            left: Box::new(subst_expr(left, mapping)),
            right: Box::new(subst_expr(right, mapping)),
        },
        Expr::Quantifier {
            kind,
            var,
            domain,
            body,
        } => {
            let sub_domain = subst_expr(domain, mapping);
            let mut inner_map = mapping.clone();
            inner_map.remove(var);
            let body_fvs = free_vars(body);
            let mut repl_fvs = BTreeSet::new();
            for (k, v) in &inner_map {
                if body_fvs.contains(k) {
                    repl_fvs.extend(free_vars(v));
                }
            }
            let (final_var, final_body) = if repl_fvs.contains(var) {
                let mut avoid = body_fvs;
                avoid.extend(repl_fvs);
                avoid.extend(inner_map.keys().cloned());
                avoid.insert(var.clone());
                let fresh = fresh_var_name(var, &avoid);
                let mut rename_map = BTreeMap::new();
                rename_map.insert(var.clone(), Expr::Var(fresh.clone()));
                let renamed_body = subst_expr(body, &rename_map);
                (fresh, subst_expr(&renamed_body, &inner_map))
            } else {
                (var.clone(), subst_expr(body, &inner_map))
            };
            Expr::Quantifier {
                kind: kind.clone(),
                var: final_var,
                domain: Box::new(sub_domain),
                body: Box::new(final_body),
            }
        }
        Expr::IfFi { branches } => Expr::IfFi {
            branches: branches
                .iter()
                .map(|b| subst_gcl_branch(b, mapping))
                .collect(),
        },
        Expr::DoOd {
            inits,
            invariant,
            variant,
            branches,
            then_expr,
        } => {
            let mut sub_inits = Vec::new();
            let mut inner_map = mapping.clone();
            for (v, ie) in inits {
                sub_inits.push((v.clone(), subst_expr(ie, &inner_map)));
                inner_map.remove(v);
            }
            Expr::DoOd {
                inits: sub_inits,
                invariant: invariant
                    .as_ref()
                    .map(|i| Box::new(subst_expr(i, &inner_map))),
                variant: variant
                    .as_ref()
                    .map(|v| Box::new(subst_expr(v, &inner_map))),
                branches: branches
                    .iter()
                    .map(|b| subst_gcl_branch(b, &inner_map))
                    .collect(),
                then_expr: Box::new(subst_expr(then_expr, &inner_map)),
            }
        }
        Expr::Match { scrutinee, arms } => Expr::Match {
            scrutinee: Box::new(subst_expr(scrutinee, mapping)),
            arms: arms
                .iter()
                .map(|arm| {
                    let mut arm_map = mapping.clone();
                    for pv in pattern_bound_vars(&arm.pattern) {
                        arm_map.remove(&pv);
                    }
                    MatchArm {
                        pattern: arm.pattern.clone(),
                        body: subst_expr(&arm.body, &arm_map),
                    }
                })
                .collect(),
        },
        Expr::RecordInit { concept, fields } => Expr::RecordInit {
            concept: concept.clone(),
            fields: fields
                .iter()
                .map(|(k, v)| (k.clone(), subst_expr(v, mapping)))
                .collect(),
        },
        Expr::RecordWith { base, updates } => Expr::RecordWith {
            base: Box::new(subst_expr(base, mapping)),
            updates: updates
                .iter()
                .map(|(k, v)| (k.clone(), subst_expr(v, mapping)))
                .collect(),
        },
        Expr::FieldAccess { base, field } => {
            let sub_base = subst_expr(base, mapping);
            // Symbolic reduction: `(base with { f: val }).f` -> `val`
            if let Expr::RecordWith {
                base: inner_base,
                updates,
            } = &sub_base
            {
                for (uk, uv) in updates.iter().rev() {
                    if uk == field {
                        return uv.clone();
                    }
                }
                return Expr::FieldAccess {
                    base: inner_base.clone(),
                    field: field.clone(),
                };
            }
            if let Expr::RecordInit { fields, .. } = &sub_base {
                for (fk, fv) in fields {
                    if fk == field {
                        return fv.clone();
                    }
                }
            }
            Expr::FieldAccess {
                base: Box::new(sub_base),
                field: field.clone(),
            }
        }
        Expr::Call { func, args } => Expr::Call {
            func: func.clone(),
            args: args.iter().map(|a| subst_expr(a, mapping)).collect(),
        },
        Expr::List(items) => Expr::List(items.iter().map(|i| subst_expr(i, mapping)).collect()),
        Expr::LetIn { name, value, body } => {
            let sub_val = subst_expr(value, mapping);
            let mut inner_map = mapping.clone();
            inner_map.remove(name);
            let body_fvs = free_vars(body);
            let mut repl_fvs = BTreeSet::new();
            for (k, v) in &inner_map {
                if body_fvs.contains(k) {
                    repl_fvs.extend(free_vars(v));
                }
            }
            let (final_name, final_body) = if repl_fvs.contains(name) {
                let mut avoid = body_fvs;
                avoid.extend(repl_fvs);
                avoid.extend(inner_map.keys().cloned());
                avoid.insert(name.clone());
                let fresh = fresh_var_name(name, &avoid);
                let mut rename_map = BTreeMap::new();
                rename_map.insert(name.clone(), Expr::Var(fresh.clone()));
                let renamed_body = subst_expr(body, &rename_map);
                (fresh, subst_expr(&renamed_body, &inner_map))
            } else {
                (name.clone(), subst_expr(body, &inner_map))
            };
            Expr::LetIn {
                name: final_name,
                value: Box::new(sub_val),
                body: Box::new(final_body),
            }
        }
    }
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

pub fn format_expr_concise(expr: &Expr) -> String {
    match expr {
        Expr::Int(v) => v.to_string(),
        Expr::Float(v) => v.to_string(),
        Expr::Bool(v) => v.to_string(),
        Expr::Str(s) => format!("\"{}\"", s),
        Expr::Var(v) => v.clone(),
        Expr::Placeholder => "_".into(),
        Expr::Unary { op, expr: inner } => match op {
            UnaryOp::Not => format!("!({})", format_expr_concise(inner)),
            UnaryOp::Neg => format!("-{}", format_expr_concise(inner)),
        },
        Expr::Binary { op, left, right } => format!(
            "({} {} {})",
            format_expr_concise(left),
            op,
            format_expr_concise(right)
        ),
        Expr::FieldAccess { base, field } => format!("{}.{}", format_expr_concise(base), field),
        Expr::Call { func, args } => {
            let s: Vec<String> = args.iter().map(format_expr_concise).collect();
            format!("{}({})", func, s.join(", "))
        }
        Expr::Quantifier {
            kind,
            var,
            domain,
            body,
        } => {
            let k = match kind {
                QuantifierKind::Forall => "forall",
                QuantifierKind::Exists => "exists",
                QuantifierKind::Choose => "choose",
            };
            format!(
                "({} {} in {} : {})",
                k,
                var,
                format_expr_concise(domain),
                format_expr_concise(body)
            )
        }
        _ => format!("{:?}", expr),
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
            .map(|script| run_smt_prover(Prover::Auto, script))
    } else {
        None
    };
    let (smt_prover, smt_verdict, agreement) = if let Some(ref res) = smt_res {
        let agr = evaluate_vc_agreement(bounded_ok, res.verdict);
        (Some(res.prover.clone()), Some(res.verdict), Some(agr))
    } else {
        (None, None, None)
    };

    let status = decide_status(ce.clone(), samples, smt_res.as_ref());
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
                                .map(|script| run_smt_prover(Prover::Auto, script))
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
                        let status = decide_status(ce_post.clone(), samples_post, smt_res.as_ref());
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
                        // Obligation A: Guard Totality: Pre => (G1 ∨ G2 ∨ ... ∨ Gn)
                        let bb = branches
                            .iter()
                            .map(|b| b.guard.clone())
                            .fold(Expr::Bool(false), disj);
                        let vc_totality = implies(pre.clone(), bb);
                        obligations.push(build_vc_obligation(
                            program,
                            ontology,
                            &f.name,
                            ObligationKind::IfFiGuardTotality,
                            &f.params,
                            &[],
                            &vc_totality,
                            false,
                            &proved_lemmas,
                            run_smt,
                        ));

                        // Obligation B: Each branch satisfies Post: (Pre ∧ Gi) => wp(Si, Post)
                        for (idx, br) in branches.iter().enumerate() {
                            let wp_s = wp_branch_body(&br.body, &post, None);
                            let vc_br = implies(conj(pre.clone(), br.guard.clone()), wp_s);
                            obligations.push(build_vc_obligation(
                                program,
                                ontology,
                                &f.name,
                                ObligationKind::IfFiBranchPostcondition(idx),
                                &f.params,
                                &[],
                                &vc_br,
                                false,
                                &proved_lemmas,
                                run_smt,
                            ));
                        }
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

                        // 1. Initialization: Pre => I[state := init]
                        let inv_init = subst_expr(&inv, &init_map);
                        let vc_init = implies(pre.clone(), inv_init);
                        obligations.push(build_vc_obligation(
                            program,
                            ontology,
                            &f.name,
                            ObligationKind::DoOdInitialization,
                            &f.params,
                            &[],
                            &vc_init,
                            false,
                            &proved_lemmas,
                            run_smt,
                        ));

                        let default_state_var = inits.first().map(|(n, _)| n.as_str());

                        // 2. Preservation & 3/4. Variant obligations per branch
                        for (idx, br) in branches.iter().enumerate() {
                            let pre_inv_g = conj(pre.clone(), conj(inv.clone(), br.guard.clone()));
                            let wp_inv = wp_branch_body(&br.body, &inv, default_state_var);
                            let vc_pres = implies(pre_inv_g.clone(), wp_inv);
                            obligations.push(build_vc_obligation(
                                program,
                                ontology,
                                &f.name,
                                ObligationKind::DoOdPreservation(idx),
                                &f.params,
                                &state_params,
                                &vc_pres,
                                false,
                                &proved_lemmas,
                                run_smt,
                            ));

                            if let Some(var_expr) = variant {
                                // Non-negativity: (Pre ∧ I ∧ Gi) => V >= 0
                                let v_non_neg = Expr::Binary {
                                    op: BinOp::Ge,
                                    left: var_expr.clone(),
                                    right: Box::new(Expr::Int(0)),
                                };
                                let vc_nn = implies(pre_inv_g.clone(), v_non_neg);
                                obligations.push(build_vc_obligation(
                                    program,
                                    ontology,
                                    &f.name,
                                    ObligationKind::DoOdVariantNonNegative(idx),
                                    &f.params,
                                    &state_params,
                                    &vc_nn,
                                    false,
                                    &proved_lemmas,
                                    run_smt,
                                ));

                                // Strict decrease: (Pre ∧ I ∧ Gi) => wp(Si, V) < V
                                let wp_v = wp_branch_body(&br.body, var_expr, default_state_var);
                                let v_dec = Expr::Binary {
                                    op: BinOp::Lt,
                                    left: Box::new(wp_v),
                                    right: var_expr.clone(),
                                };
                                let vc_dec = implies(pre_inv_g, v_dec);
                                obligations.push(build_vc_obligation(
                                    program,
                                    ontology,
                                    &f.name,
                                    ObligationKind::DoOdVariantDecrease(idx),
                                    &f.params,
                                    &state_params,
                                    &vc_dec,
                                    false,
                                    &proved_lemmas,
                                    run_smt,
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
                        obligations.push(build_vc_obligation(
                            program,
                            ontology,
                            &f.name,
                            ObligationKind::DoOdExitPostcondition,
                            &f.params,
                            &state_params,
                            &vc_exit,
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
                                    .map(|script| run_smt_prover(Prover::Auto, script))
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
                            let status = decide_status(ce.clone(), samples, smt_res.as_ref());
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

/// Bounded symbolic/exhaustive domain solver for Verification Conditions
fn check_vc_bounded(
    program: &Program,
    ontology: &OntologyRegistry,
    fn_params: &[Param],
    state_params: &[Param],
    vc: &Expr,
) -> (bool, Option<String>, usize) {
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
    let samples = domains
        .iter()
        .map(|(_, vals)| vals.len().max(1))
        .product::<usize>();

    let mut interp = Interpreter::new(ontology.clone(), 42, false);
    let _ = interp.run_program(&Program {
        items: program
            .items
            .iter()
            .filter(|i| matches!(i, Item::TypeDecl(_) | Item::FnDecl(_) | Item::Spec(_)))
            .cloned()
            .collect(),
    });

    let mut env = BTreeMap::new();
    let (ok, ce) = search_counterexample(&mut interp, &domains, 0, &mut env, vc);
    (ok, ce, samples)
}

fn check_refinement_execution(
    program: &Program,
    ontology: &OntologyRegistry,
    f: &FnDecl,
    post: &Expr,
) -> (bool, Option<String>, usize) {
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
    let samples = domains
        .iter()
        .map(|(_, vals)| vals.len().max(1))
        .product::<usize>();

    let mut interp = Interpreter::new(ontology.clone(), 42, false);
    let _ = interp.run_program(&Program {
        items: program
            .items
            .iter()
            .filter(|i| matches!(i, Item::TypeDecl(_) | Item::FnDecl(_) | Item::Spec(_)))
            .cloned()
            .collect(),
    });

    let pre = f.requires.clone().unwrap_or(Expr::Bool(true));
    let mut env = BTreeMap::new();
    let (ok, ce) = search_fn_post(&mut interp, &domains, 0, &mut env, f, &pre, post);
    (ok, ce, samples)
}

fn search_fn_post(
    interp: &mut Interpreter,
    domains: &[(String, Vec<Value>)],
    idx: usize,
    env: &mut BTreeMap<String, Value>,
    f: &FnDecl,
    pre: &Expr,
    post: &Expr,
) -> (bool, Option<String>) {
    if idx >= domains.len() {
        if interp.eval_expr(pre, env).unwrap_or(Value::Bool(false)) != Value::Bool(true) {
            return (true, None);
        }
        match interp.eval_expr(&f.body, env) {
            Ok(res) => {
                let mut post_env = env.clone();
                post_env.insert("result".into(), res.clone());
                match interp.eval_expr(post, &post_env) {
                    Ok(Value::Bool(true)) => (true, None),
                    _ => (false, Some(format_env_assignment(&post_env))),
                }
            }
            Err(e) => (false, Some(format!("{} -> {}", format_env_assignment(env), e))),
        }
    } else {
        let (vname, vals) = &domains[idx];
        for v in vals {
            env.insert(vname.clone(), v.clone());
            let (ok, ce) = search_fn_post(interp, domains, idx + 1, env, f, pre, post);
            if !ok {
                return (false, ce);
            }
        }
        env.remove(vname);
        (true, None)
    }
}

fn search_counterexample(
    interp: &mut Interpreter,
    domains: &[(String, Vec<Value>)],
    idx: usize,
    env: &mut BTreeMap<String, Value>,
    vc: &Expr,
) -> (bool, Option<String>) {
    if idx >= domains.len() {
        match interp.eval_expr(vc, env) {
            Ok(Value::Bool(true)) => (true, None),
            Ok(Value::Bool(false)) => (false, Some(format_env_assignment(env))),
            Ok(other) => (
                false,
                Some(format!(
                    "{} -> non-boolean VC: {}",
                    format_env_assignment(env),
                    other
                )),
            ),
            Err(e) => (false, Some(format!("{} -> {}", format_env_assignment(env), e))),
        }
    } else {
        let (vname, vals) = &domains[idx];
        for v in vals {
            env.insert(vname.clone(), v.clone());
            let (ok, ce) = search_counterexample(interp, domains, idx + 1, env, vc);
            if !ok {
                return (false, ce);
            }
        }
        env.remove(vname);
        (true, None)
    }
}

fn format_env_assignment(env: &BTreeMap<String, Value>) -> String {
    let parts: Vec<String> = env.iter().map(|(k, v)| format!("{} = {}", k, v)).collect();
    format!("{{ {} }}", parts.join(", "))
}

/// Extracts integer constants `c` and their immediate neighbors `c - 1, c, c + 1` from an expression
/// so bounded counterexample search automatically probes threshold boundaries.
fn extract_int_constants(expr: &Expr, out: &mut BTreeSet<i64>) {
    match expr {
        Expr::Int(c) => {
            for v in [c.saturating_sub(1), *c, c.saturating_add(1)] {
                if out.len() < 24 {
                    out.insert(v);
                }
            }
        }
        Expr::Unary {
            op: UnaryOp::Neg,
            expr: inner,
        } => {
            if let Expr::Int(c) = &**inner {
                let nc = c.saturating_neg();
                for v in [nc.saturating_sub(1), nc, nc.saturating_add(1)] {
                    if out.len() < 24 {
                        out.insert(v);
                    }
                }
            } else {
                extract_int_constants(inner, out);
            }
        }
        Expr::Unary { expr: inner, .. } => extract_int_constants(inner, out),
        Expr::Binary { left, right, .. } => {
            extract_int_constants(left, out);
            extract_int_constants(right, out);
        }
        Expr::Quantifier { domain, body, .. } => {
            extract_int_constants(domain, out);
            extract_int_constants(body, out);
        }
        Expr::FieldAccess { base, .. } => extract_int_constants(base, out),
        Expr::RecordInit { fields, .. } => {
            for (_, v) in fields {
                extract_int_constants(v, out);
            }
        }
        Expr::RecordWith { base, updates } => {
            extract_int_constants(base, out);
            for (_, v) in updates {
                extract_int_constants(v, out);
            }
        }
        Expr::Call { args, .. } | Expr::List(args) => {
            for a in args {
                extract_int_constants(a, out);
            }
        }
        Expr::LetIn { value, body, .. } => {
            extract_int_constants(value, out);
            extract_int_constants(body, out);
        }
        Expr::Match { scrutinee, arms } => {
            extract_int_constants(scrutinee, out);
            for a in arms {
                extract_int_constants(&a.body, out);
            }
        }
        Expr::IfFi { branches } => {
            for br in branches {
                extract_int_constants(&br.guard, out);
                if let GclBody::Expr(e) = &br.body {
                    extract_int_constants(e, out);
                }
            }
        }
        Expr::DoOd {
            inits,
            invariant,
            variant,
            branches,
            then_expr,
        } => {
            for (_, ie) in inits {
                extract_int_constants(ie, out);
            }
            if let Some(inv) = invariant {
                extract_int_constants(inv, out);
            }
            if let Some(var) = variant {
                extract_int_constants(var, out);
            }
            for br in branches {
                extract_int_constants(&br.guard, out);
                if let GclBody::Expr(e) = &br.body {
                    extract_int_constants(e, out);
                }
            }
            extract_int_constants(then_expr, out);
        }
        _ => {}
    }
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
