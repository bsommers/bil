use crate::ast::*;
use crate::ontology::OntologyRegistry;
use std::collections::BTreeSet;
use std::env;
use std::fmt;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

/// Tri-state verdict model ported from `clif2OntoLogic/verify/prover.py` (ADR 0002)
/// and `OntoLogic/src/Solver.hs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Satisfiable (`sat` in Z3/CVC5 or model found by Mace4)
    Consistent,
    /// Unsatisfiable (`unsat` in Z3/CVC5 or refutation found by Prover9)
    Inconsistent,
    /// Timeout, resource limit, or inconclusive search
    Unknown,
    /// Prover binary not installed on host
    Skipped,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Verdict::Consistent => write!(f, "consistent (SAT)"),
            Verdict::Inconsistent => write!(f, "inconsistent (UNSAT)"),
            Verdict::Unknown => write!(f, "unknown"),
            Verdict::Skipped => write!(f, "skipped"),
        }
    }
}

/// Comparative solver agreement outcome ported from `clif2OntoLogic/verify/comparator.py` (VERIFY-04)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgreementOutcome {
    /// Both bounded model finder and unbounded SMT solver agree
    Match,
    /// One or both solvers returned Unknown
    Inconclusive,
    /// Critical disagreement between solvers (SAT vs UNSAT)
    Disagreement,
    /// External solver binary not installed
    Skipped,
}

impl fmt::Display for AgreementOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AgreementOutcome::Match => write!(f, "MATCH"),
            AgreementOutcome::Inconclusive => write!(f, "INCONCLUSIVE"),
            AgreementOutcome::Disagreement => write!(f, "DISAGREEMENT"),
            AgreementOutcome::Skipped => write!(f, "SKIPPED"),
        }
    }
}

/// Supported automated theorem prover backends (`OntoLogic/src/Solver.hs` + `clif2OntoLogic`)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Prover {
    Z3,
    Cvc5,
    Vampire,
    Auto,
}

impl Prover {
    pub fn parse(s: &str) -> Self {
        match s.to_ascii_lowercase().as_str() {
            "z3" => Prover::Z3,
            "cvc5" => Prover::Cvc5,
            "vampire" => Prover::Vampire,
            _ => Prover::Auto,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Prover::Z3 => "z3",
            Prover::Cvc5 => "cvc5",
            Prover::Vampire => "vampire",
            Prover::Auto => "auto(z3->cvc5->vampire)",
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProverResult {
    pub prover: String,
    pub verdict: Verdict,
    pub stdout: String,
    pub stderr: String,
    pub elapsed_ms: u128,
    pub detail: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubsumptionResult {
    Subsumed { prover: String },
    NotSubsumed { prover: String, witness: String },
    Unknown { detail: String },
}

/// Resolves an external solver binary using configurable resolution order:
/// 1. `BIL_<NAME>_PATH`, `BIL_<NAME>`, or `CLIF2OL_<NAME>` environment variable
/// 2. `BIL_SOLVER_DIR/<name>` directory override
/// 3. `~/.local/bin/<name>`
/// 4. `PATH` lookup
pub fn find_solver_binary(name: &str) -> Option<PathBuf> {
    let upper = name.to_ascii_uppercase().replace('-', "_");
    for env_key in [
        format!("BIL_{}_PATH", upper),
        format!("BIL_{}", upper),
        format!("CLIF2OL_{}", upper),
    ] {
        if let Ok(val) = env::var(&env_key) {
            let p = PathBuf::from(val.trim());
            if p.is_file() {
                return Some(p);
            }
        }
    }

    if let Ok(dir) = env::var("BIL_SOLVER_DIR") {
        let candidate = Path::new(dir.trim()).join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    if let Ok(home) = env::var("HOME") {
        let local_bin = Path::new(&home).join(".local/bin").join(name);
        if local_bin.is_file() {
            return Some(local_bin);
        }
    }

    if let Ok(path_var) = env::var("PATH") {
        for dir in env::split_paths(&path_var) {
            let candidate = dir.join(name);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }

    None
}

/// Runs raw SMT-LIB2 input through the selected solver backend (`OntoLogic/Solver.hs::runProver`
/// + `clif2OntoLogic/verify/prover.py::run_z3`).
pub fn run_smt_prover(prover: Prover, smt2_input: &str) -> ProverResult {
    match prover {
        Prover::Z3 => run_single_binary(
            "z3",
            &["-in", "-T:5"],
            smt2_input,
        ),
        Prover::Cvc5 => run_single_binary(
            "cvc5",
            &["--lang=smt2", "--produce-models", "--tlimit=5000", "-"],
            smt2_input,
        ),
        Prover::Vampire => run_single_binary(
            "vampire",
            &["--input_syntax", "smtlib2", "--mode", "smtcomp", "-t", "5"],
            smt2_input,
        ),
        Prover::Auto => {
            let z3_res = run_smt_prover(Prover::Z3, smt2_input);
            if z3_res.verdict != Verdict::Skipped {
                return z3_res;
            }
            let cvc5_res = run_smt_prover(Prover::Cvc5, smt2_input);
            if cvc5_res.verdict != Verdict::Skipped {
                return cvc5_res;
            }
            run_smt_prover(Prover::Vampire, smt2_input)
        }
    }
}

fn run_single_binary(bin_name: &str, args: &[&str], smt2_input: &str) -> ProverResult {
    let Some(bin_path) = find_solver_binary(bin_name) else {
        return ProverResult {
            prover: bin_name.to_string(),
            verdict: Verdict::Skipped,
            stdout: String::new(),
            stderr: String::new(),
            elapsed_ms: 0,
            detail: format!("{} binary not found", bin_name),
        };
    };

    let start = Instant::now();
    let mut child = match Command::new(&bin_path)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            return ProverResult {
                prover: bin_name.to_string(),
                verdict: Verdict::Unknown,
                stdout: String::new(),
                stderr: e.to_string(),
                elapsed_ms: start.elapsed().as_millis(),
                detail: format!("Failed to spawn {}: {}", bin_name, e),
            };
        }
    };

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(smt2_input.as_bytes());
    }

    match child.wait_with_output() {
        Ok(out) => {
            let elapsed_ms = start.elapsed().as_millis();
            let stdout = String::from_utf8_lossy(&out.stdout).to_string();
            let stderr = String::from_utf8_lossy(&out.stderr).to_string();

            let mut verdict = Verdict::Unknown;
            let mut detail = format!("{} inconclusive", bin_name);

            if stdout.contains("(error") || stderr.contains("(error") {
                verdict = Verdict::Unknown;
                detail = format!("{} reported SMT-LIB error", bin_name);
            } else {
                for line in stdout.lines().map(str::trim).filter(|l| !l.is_empty()) {
                    if line == "sat" || line.starts_with("sat") {
                        verdict = Verdict::Consistent;
                        detail = format!("{} found satisfying model (sat)", bin_name);
                        break;
                    }
                    if line == "unsat" || line.starts_with("unsat") {
                        verdict = Verdict::Inconsistent;
                        detail = format!("{} proved unsatisfiable (unsat)", bin_name);
                        break;
                    }
                    if line == "unknown" || line.to_ascii_lowercase().contains("timeout") {
                        verdict = Verdict::Unknown;
                        detail = format!("{} returned unknown/timeout", bin_name);
                        break;
                    }
                }
            }

            ProverResult {
                prover: bin_name.to_string(),
                verdict,
                stdout,
                stderr,
                elapsed_ms,
                detail,
            }
        }
        Err(e) => ProverResult {
            prover: bin_name.to_string(),
            verdict: Verdict::Unknown,
            stdout: String::new(),
            stderr: e.to_string(),
            elapsed_ms: start.elapsed().as_millis(),
            detail: format!("Wait failed: {}", e),
        },
    }
}

/// Evaluates agreement between bounded counterexample search and unbounded SMT refutation
/// (`clif2OntoLogic/verify/comparator.py::evaluate_agreement`).
/// Note: For a Verification Condition (VC), `verified == true` corresponds to `!(VC)` being `Inconsistent` (`unsat`).
pub fn evaluate_vc_agreement(bounded_verified: bool, smt_refutation_verdict: Verdict) -> AgreementOutcome {
    match smt_refutation_verdict {
        Verdict::Skipped => AgreementOutcome::Skipped,
        Verdict::Unknown => AgreementOutcome::Inconclusive,
        Verdict::Inconsistent => {
            // Refutation `not(VC)` is UNSAT => VC is universally valid!
            if bounded_verified {
                AgreementOutcome::Match
            } else {
                AgreementOutcome::Disagreement
            }
        }
        Verdict::Consistent => {
            // Refutation `not(VC)` is SAT => SMT found a counterexample!
            // If bounded search also found a counterexample (`!bounded_verified`), they MATCH.
            if !bounded_verified {
                AgreementOutcome::Match
            } else {
                // SMT found an out-of-bounds counterexample that small-domain sampling missed, or uninterpreted functions were unconstrained
                AgreementOutcome::Inconclusive
            }
        }
    }
}

/// Sanitizes an identifier for SMT-LIB2 (`clif2OntoLogic/verify/smt.py::sanitize_smt_ident`).
pub fn sanitize_smt_ident(name: &str) -> String {
    let mut s: String = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if s.is_empty() {
        s = "id".to_string();
    }
    if s.chars().next().unwrap().is_ascii_digit() {
        s = format!("n_{}", s);
    }
    s
}

/// Emits the base SMT-LIB2 ontology encoding (`OntoLogic/src/Solver.hs::emitSMTBase` +
/// `clif2OntoLogic/verify/smt.py` guarded quantifier relativization).
pub fn emit_ontology_smt2_base(program: &Program, ontology: &OntologyRegistry) -> String {
    let mut lines = Vec::new();
    lines.push(";; SMT-LIB2 Base Theory generated by `bil` (OntoLogic + clif2OntoLogic Solver Bridge)".to_string());
    lines.push("(set-logic ALL)".to_string());
    lines.push("(declare-sort Entity 0)".to_string());
    lines.push("(declare-fun subClassOf (Entity Entity) Bool)".to_string());

    // Reflexivity & Transitivity of `subClassOf` (`OntoLogic/src/Solver.hs` lines 155-160)
    lines.push("(assert (forall ((x Entity)) (subClassOf x x)))".to_string());
    lines.push(
        "(assert (forall ((x Entity) (y Entity) (z Entity)) (=> (and (subClassOf x y) (subClassOf y z)) (subClassOf x z))))"
            .to_string(),
    );

    // Pass 1: Declare all concept constants, membership predicates, and field accessors first
    let mut declared_fields = BTreeSet::new();
    for (cname, cinfo) in &ontology.concepts {
        let cid = sanitize_smt_ident(cname);
        lines.push(format!("(declare-const {} Entity)", cid));
        lines.push(format!("(declare-fun is_{} (Entity) Bool)", cid));
        for (fname, fty) in &cinfo.all_fields {
            let fid = format!("field_{}", sanitize_smt_ident(fname));
            if declared_fields.insert(fid.clone()) {
                let smt_ty = map_type_to_smt(fty, ontology);
                lines.push(format!("(declare-fun {} (Entity) {})", fid, smt_ty));
            }
        }
    }

    // Pass 2: Emit taxonomic hierarchy & guarded subsumption assertions (`OntoLogic/Solver.hs` + `clif2OntoLogic/verify/smt.py`)
    for (cname, cinfo) in &ontology.concepts {
        if let Some(parent) = &cinfo.parent {
            let cid = sanitize_smt_ident(cname);
            let pid = sanitize_smt_ident(parent);
            lines.push(format!("(assert (subClassOf {} {}))", cid, pid));
            lines.push(format!(
                "(assert (forall ((x Entity)) (=> (is_{} x) (is_{} x))))",
                cid, pid
            ));
        }
    }

    // Emit FOL `axiom` declarations with guarded quantifier relativization (`clif2OntoLogic/verify/smt.py`)
    for item in &program.items {
        if let Item::Axiom(ax) = item {
            if let Some(smt_ax) = expr_to_smt(&ax.formula, ontology, None) {
                lines.push(format!(";; axiom {}", ax.name));
                lines.push(format!("(assert {})", smt_ax));
            }
        }
    }

    lines.join("\n") + "\n"
}

/// Emits complete SMT-LIB2 script for checking ontology consistency (`OntoLogic/Solver.hs::emitSMTForConsistency`).
pub fn emit_ontology_consistency_smt2(program: &Program, ontology: &OntologyRegistry) -> String {
    let mut s = emit_ontology_smt2_base(program, ontology);
    // Witness at least one instance per declared concept so single-concept axiom contradictions trigger UNSAT
    for cname in ontology.concepts.keys() {
        let cid = sanitize_smt_ident(cname);
        s.push_str(&format!("(declare-const witness_{} Entity)\n", cid));
        s.push_str(&format!("(assert (is_{} witness_{}))\n", cid, cid));
    }
    s.push_str("(check-sat)\n");
    s
}

/// Checks ontology consistency using the selected SMT prover (`OntoLogic/Solver.hs::checkConsistencyWith`).
pub fn check_ontology_consistency(
    program: &Program,
    ontology: &OntologyRegistry,
    prover: Prover,
) -> ProverResult {
    let smt = emit_ontology_consistency_smt2(program, ontology);
    run_smt_prover(prover, &smt)
}

/// Proves whether `child` is subsumed by `parent` ($A \sqsubseteq B$) via refutation (`OntoLogic/Solver.hs::proveSubsumptionWith`).
pub fn prove_subsumption(
    program: &Program,
    ontology: &OntologyRegistry,
    child: &str,
    parent: &str,
    prover: Prover,
) -> SubsumptionResult {
    let mut smt = emit_ontology_smt2_base(program, ontology);
    let cid = sanitize_smt_ident(child);
    let pid = sanitize_smt_ident(parent);
    smt.push_str(&format!(
        ";; Negation of Subsumption Goal: NOT (subClassOf {} {})\n",
        cid, pid
    ));
    smt.push_str(&format!("(assert (not (subClassOf {} {})))\n", cid, pid));
    smt.push_str("(check-sat)\n");

    let res = run_smt_prover(prover, &smt);
    match res.verdict {
        Verdict::Inconsistent => SubsumptionResult::Subsumed { prover: res.prover },
        Verdict::Consistent => SubsumptionResult::NotSubsumed {
            prover: res.prover,
            witness: res.stdout,
        },
        _ => SubsumptionResult::Unknown { detail: res.detail },
    }
}

/// Emits an SMT-LIB2 refutation script for a Dijkstra `wp` or Verus `proof` Verification Condition (`VC`).
/// Proves validity of `VC` by checking unsatisfiability (`unsat`) of `(not VC)`.
pub fn emit_vc_smt2(
    program: &Program,
    ontology: &OntologyRegistry,
    params: &[Param],
    vc: &Expr,
    include_axioms: bool,
    proved_lemmas: &[ProofDecl],
) -> Option<String> {
    let vc_smt = expr_to_smt(vc, ontology, None)?;
    let mut lines = Vec::new();
    if include_axioms {
        lines.push(emit_ontology_smt2_base(program, ontology));
    } else {
        lines.push("(set-logic ALL)".to_string());
        lines.push("(declare-sort Entity 0)".to_string());
        let mut declared_fields = BTreeSet::new();
        for (cname, cinfo) in &ontology.concepts {
            let cid = sanitize_smt_ident(cname);
            lines.push(format!("(declare-fun is_{} (Entity) Bool)", cid));
            for (fname, fty) in &cinfo.all_fields {
                let fid = format!("field_{}", sanitize_smt_ident(fname));
                if declared_fields.insert(fid.clone()) {
                    let smt_ty = map_type_to_smt(fty, ontology);
                    lines.push(format!("(declare-fun {} (Entity) {})", fid, smt_ty));
                }
            }
        }
        for (cname, cinfo) in &ontology.concepts {
            if let Some(parent) = &cinfo.parent {
                let cid = sanitize_smt_ident(cname);
                let pid = sanitize_smt_ident(parent);
                lines.push(format!(
                    "(assert (forall ((x Entity)) (=> (is_{} x) (is_{} x))))",
                    cid, pid
                ));
            }
        }
    }

    let mut seen = BTreeSet::new();
    for item in &program.items {
        if let Item::TypeDecl(adt) = item {
            if adt.variants.iter().all(|v| v.payload.is_empty()) {
                for (idx, v) in adt.variants.iter().enumerate() {
                    let vname = sanitize_smt_ident(&v.name);
                    if seen.insert(vname.clone()) {
                        lines.push(format!("(define-const {} Int {})", vname, idx));
                    }
                }
            }
        }
    }
    for p in params {
        let vname = sanitize_smt_ident(&p.name);
        if seen.insert(vname.clone()) {
            let smt_ty = map_type_to_smt(&p.ty, ontology);
            lines.push(format!("(declare-const {} {})", vname, smt_ty));
            if let TypeExpr::Named(cname) = &p.ty {
                if ontology.concepts.contains_key(cname) {
                    lines.push(format!(
                        "(assert (is_{} {}))",
                        sanitize_smt_ident(cname),
                        vname
                    ));
                }
            }
        }
    }

    // Only include previously SMT-proved parameterless `proof` lemmas as assumptions
    for pr in proved_lemmas {
        if pr.params.is_empty() {
            let lemma_formula = match &pr.requires {
                Some(req) => Expr::Binary {
                    op: BinOp::Implies,
                    left: Box::new(req.clone()),
                    right: Box::new(pr.ensures.clone()),
                },
                None => pr.ensures.clone(),
            };
            if let Some(lemma_smt) = expr_to_smt(&lemma_formula, ontology, None) {
                lines.push(format!(";; proved lemma {}", pr.name));
                lines.push(format!("(assert {})", lemma_smt));
            }
        }
    }

    lines.push(format!(";; Refutation of VC: {}", crate::wp::format_expr_concise(vc)));
    lines.push(format!("(assert (not {}))", vc_smt));
    lines.push("(check-sat)".to_string());
    Some(lines.join("\n") + "\n")
}

fn map_type_to_smt(ty: &TypeExpr, ontology: &OntologyRegistry) -> String {
    match ty {
        TypeExpr::Named(n) => match n.as_str() {
            "Int" | "Integer" => "Int".to_string(),
            "Float" | "Double" => "Real".to_string(),
            "Bool" | "Boolean" => "Bool".to_string(),
            "String" | "Str" => "String".to_string(),
            other if ontology.concepts.contains_key(other) => "Entity".to_string(),
            _ => "Int".to_string(),
        },
        _ => "Int".to_string(),
    }
}

/// Translates a `bil` AST `Expr` into SMT-LIB2 syntax (`OntoLogic/Emitters/SMT.hs::emitFOLToSMT`
/// + `clif2OntoLogic/verify/smt.py::sentence_to_smtlib2`).
pub fn expr_to_smt(
    expr: &Expr,
    ontology: &OntologyRegistry,
    entity_var: Option<&str>,
) -> Option<String> {
    match expr {
        Expr::Int(v) => {
            if *v < 0 {
                Some(format!("(- {})", -v))
            } else {
                Some(v.to_string())
            }
        }
        Expr::Float(v) => {
            let s = format!("{}", v);
            let s = if s.contains('.') { s } else { format!("{}.0", s) };
            Some(s)
        }
        Expr::Bool(b) => Some(b.to_string()),
        Expr::Str(s) => Some(format!("\"{}\"", s.replace('"', ""))),
        Expr::Var(v) => Some(sanitize_smt_ident(v)),
        Expr::Unary { op, expr: inner } => {
            let sub = expr_to_smt(inner, ontology, entity_var)?;
            match op {
                UnaryOp::Not => Some(format!("(not {})", sub)),
                UnaryOp::Neg => Some(format!("(- {})", sub)),
            }
        }
        Expr::Binary { op, left, right } => {
            let l = expr_to_smt(left, ontology, entity_var)?;
            let r = expr_to_smt(right, ontology, entity_var)?;
            let smt_op = match op {
                BinOp::Implies => "=>",
                BinOp::Iff | BinOp::Eq => "=",
                BinOp::Neq => "distinct",
                BinOp::And => "and",
                BinOp::Or => "or",
                BinOp::Lt => "<",
                BinOp::Le => "<=",
                BinOp::Gt => ">",
                BinOp::Ge => ">=",
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "div",
                BinOp::Mod => "mod",
                _ => return None,
            };
            Some(format!("({} {} {})", smt_op, l, r))
        }
        Expr::FieldAccess { base, field } => {
            let b = expr_to_smt(base, ontology, entity_var)?;
            let fid = format!("field_{}", sanitize_smt_ident(field));
            Some(format!("({} {})", fid, b))
        }
        Expr::Quantifier {
            kind,
            var,
            domain,
            body,
        } => {
            let vname = sanitize_smt_ident(var);
            let smt_q = match kind {
                QuantifierKind::Forall => "forall",
                QuantifierKind::Exists | QuantifierKind::Choose => "exists",
            };

            // Case 1: Concept domain `forall x in Concept : Body(x)` -> guarded relativization (`clif2OntoLogic/verify/smt.py`)
            if let Expr::Var(cname) = &**domain {
                if ontology.concepts.contains_key(cname) {
                    let cid = sanitize_smt_ident(cname);
                    let inner = expr_to_smt(body, ontology, Some(&vname))?;
                    let relativized = if matches!(kind, QuantifierKind::Forall) {
                        format!("(=> (is_{} {}) {})", cid, vname, inner)
                    } else {
                        format!("(and (is_{} {}) {})", cid, vname, inner)
                    };
                    return Some(format!("({} (({} Entity)) {})", smt_q, vname, relativized));
                }
            }

            // Case 2: Bounded integer range `forall x in lo..=hi : Body(x)`
            if let Expr::Binary {
                op: BinOp::RangeInc,
                left,
                right,
            } = &**domain
            {
                let lo = expr_to_smt(left, ontology, entity_var)?;
                let hi = expr_to_smt(right, ontology, entity_var)?;
                let inner = expr_to_smt(body, ontology, entity_var)?;
                let guard = format!("(and (>= {} {}) (<= {} {}))", vname, lo, vname, hi);
                let relativized = if matches!(kind, QuantifierKind::Forall) {
                    format!("(=> {} {})", guard, inner)
                } else {
                    format!("(and {} {})", guard, inner)
                };
                return Some(format!("({} (({} Int)) {})", smt_q, vname, relativized));
            }

            None
        }
        Expr::Call { func, args } => {
            let b = crate::builtins::BuiltinFn::from_name(func)?;
            let mut smt_args = Vec::with_capacity(args.len());
            for a in args {
                smt_args.push(expr_to_smt(a, ontology, entity_var)?);
            }
            b.to_smt(&smt_args, args)
        }
        Expr::LetIn { name, value, body } => {
            let v = expr_to_smt(value, ontology, entity_var)?;
            let b = expr_to_smt(body, ontology, entity_var)?;
            Some(format!("(let (({} {})) {})", sanitize_smt_ident(name), v, b))
        }
        _ => None,
    }
}
