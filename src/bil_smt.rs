//! Fragment classifier, finite `Entity` quantifier instantiator, and decision procedure for the
//! in-repo `bil-smt` backend (Roadmap 8.1.2 & 8.1.3).
//!
//! ## Decidable Fragment (`Fragment`)
//! An SMT-LIB2 script is in the `bil-smt` fragment iff:
//! 1. **Sorts**: Only `Int`, `Bool`, `String` (only in equality/disequality and `ite`, or in
//!    `declare-fun`/`declare-const` signatures — no string concatenation, length, or regex), and
//!    at most one uninterpreted sort `Entity`.
//! 2. **Declarations**:
//!    - `(set-logic ALL)`
//!    - `(declare-sort Entity 0)`
//!    - `(declare-const <id> Int|Bool|Entity|String)`
//!    - `(define-const <id> Int <int-literal>)`
//!    - `(declare-fun <id> () Int|Bool|Entity|String)`
//!    - `(declare-fun <id> (Entity ... Entity) Int|Bool|String)` (at least 1 arg, all args `Entity`;
//!      no uninterpreted function may return `Entity`)
//! 3. **Commands**: `(assert <term>)`, `(push 1)` / `(push)`, `(pop 1)` / `(pop)`, `(check-sat)`,
//!    and `(get-model)`.
//! 4. **Terms & Formulas**:
//!    - Boolean connectives: `true`, `false`, `not`, `and`, `or`, `=>`, `=` (on `Bool`, `Int`,
//!      `Entity`, or `String`), `distinct` (on `Bool`, `Int`, `Entity`, or `String`), `ite`.
//!    - Linear integer arithmetic: integer literals `n` and `(- n)`, unary `-`, binary `+`, `-`,
//!      `*` where at least one operand is an integer literal constant, `div` and `mod` where the
//!      divisor is a positive integer literal constant, `abs`, and comparisons `<`, `<=`, `>`, `>=`.
//!    - String literals `"..."` (participating only in `=`, `distinct`, `ite`, `let`, or function
//!      return values — decidable by finite constant/congruence numbering).
//!    - Local bindings: `(let ((<var> <term>) ...) <body>)` where bound terms are in the fragment.
//!    - Uninterpreted applications `(f t_1 ... t_k)` where `f` is a declared function over `Entity`
//!      with `Int`, `Bool`, or `String` result and each `t_i` is a term of sort `Entity`.
//!    - Universal quantifiers `(forall ((x_1 Entity) ... (x_k Entity)) <body>)` where every bound
//!      variable has sort `Entity` and `<body>` is in the fragment (including nested `forall` over
//!      `Entity`, but no `exists` and no `forall` over `Int` or other sorts).
//!
//! Because no function symbol returns `Entity` and no `exists` quantifier is present, the Herbrand
//! universe for sort `Entity` is finite and consists of the declared `Entity` constants (or a single
//! fresh witness constant if none are declared). Replacing each `(forall ((x Entity)) body)` with the
//! conjunction of its instances over those constants is equisatisfiable and produces a quantifier-free
//! `QF_UFLIA` script, which is then lowered via Ackermannization and solved by DPLL(T) + exact `QF_LIA`
//! (bound propagation + exact Fourier-Motzkin / Omega elimination with model verification).

use crate::smt::{parse_sexprs, ProverResult, SExpr, Verdict};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtSort {
    Int,
    Bool,
    Entity,
    String,
}

impl SmtSort {
    fn parse(s: &str) -> Option<Self> {
        match s {
            "Int" => Some(SmtSort::Int),
            "Bool" => Some(SmtSort::Bool),
            "Entity" => Some(SmtSort::Entity),
            "String" => Some(SmtSort::String),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunSig {
    pub args: Vec<SmtSort>,
    pub ret: SmtSort,
}

/// Reason a script lies outside the decidable `bil-smt` fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OutOfFragment {
    ParseError,
    UnsupportedCommand(String),
    UnsupportedSort(String),
    FunctionReturnsEntity(String),
    FunctionNonEntityArg(String),
    QuantifierNotForallEntity(String),
    NonlinearMultiplication,
    NonConstantDivMod,
    UnknownSymbol(String),
    TypeMismatch(String),
    UnsupportedTerm(String),
}

impl std::fmt::Display for OutOfFragment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutOfFragment::ParseError => write!(f, "malformed SMT-LIB2 S-expression"),
            OutOfFragment::UnsupportedCommand(c) => write!(f, "unsupported command `{}`", c),
            OutOfFragment::UnsupportedSort(s) => write!(f, "unsupported sort `{}`", s),
            OutOfFragment::FunctionReturnsEntity(n) => {
                write!(f, "function `{}` returns Entity (unbounded Herbrand universe)", n)
            }
            OutOfFragment::FunctionNonEntityArg(n) => {
                write!(f, "uninterpreted function `{}` has non-Entity argument sort", n)
            }
            OutOfFragment::QuantifierNotForallEntity(q) => {
                write!(f, "quantifier `{}` outside forall-Entity fragment", q)
            }
            OutOfFragment::NonlinearMultiplication => {
                write!(f, "nonlinear multiplication (neither operand is an Int constant)")
            }
            OutOfFragment::NonConstantDivMod => {
                write!(f, "div/mod by non-constant or non-positive divisor")
            }
            OutOfFragment::UnknownSymbol(s) => write!(f, "unknown symbol `{}`", s),
            OutOfFragment::TypeMismatch(m) => write!(f, "type mismatch: {}", m),
            OutOfFragment::UnsupportedTerm(t) => write!(f, "unsupported term `{}`", t),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Scope {
    consts: BTreeMap<String, SmtSort>,
    defined_ints: BTreeMap<String, i64>,
    funs: BTreeMap<String, FunSig>,
    entity_consts: Vec<String>,
    assertions: Vec<SExpr>,
}

/// Checks whether `smt2_input` belongs to the `bil-smt` decidable fragment and, if so, returns the
/// quantifier-free SMT-LIB2 script obtained by instantiating every `forall ((x Entity))` over the
/// declared `Entity` constants (introducing one fresh witness constant if `Entity` is used with no
/// declared constants).
pub fn instantiate_entity_quantifiers(smt2_input: &str) -> Result<String, OutOfFragment> {
    let forms = parse_sexprs(smt2_input).ok_or(OutOfFragment::ParseError)?;

    // First pass: validate all commands and collect all declared Entity constants across the script
    // (in bil's emitted scripts, all declarations precede assertions, or occur before push/pop).
    let mut scope = Scope::default();
    let mut stack: Vec<Scope> = Vec::new();
    let mut uses_entity_quantifier = false;

    for form in &forms {
        let SExpr::List(items) = form else {
            return Err(OutOfFragment::ParseError);
        };
        let Some(SExpr::Atom(cmd)) = items.first() else {
            return Err(OutOfFragment::ParseError);
        };
        match cmd.as_str() {
            "set-logic" => {}
            "declare-sort" => {
                if items.len() != 3 {
                    return Err(OutOfFragment::UnsupportedCommand("declare-sort".into()));
                }
                if let (SExpr::Atom(name), SExpr::Atom(arity)) = (&items[1], &items[2]) {
                    if name != "Entity" || arity != "0" {
                        return Err(OutOfFragment::UnsupportedSort(name.clone()));
                    }
                } else {
                    return Err(OutOfFragment::UnsupportedCommand("declare-sort".into()));
                }
            }
            "declare-const" => {
                if items.len() != 3 {
                    return Err(OutOfFragment::UnsupportedCommand("declare-const".into()));
                }
                let (SExpr::Atom(name), SExpr::Atom(sort_name)) = (&items[1], &items[2]) else {
                    return Err(OutOfFragment::UnsupportedCommand("declare-const".into()));
                };
                let sort = SmtSort::parse(sort_name)
                    .ok_or_else(|| OutOfFragment::UnsupportedSort(sort_name.clone()))?;
                if sort == SmtSort::Entity && !scope.entity_consts.contains(name) {
                    scope.entity_consts.push(name.clone());
                }
                scope.consts.insert(name.clone(), sort);
            }
            "define-const" => {
                if items.len() != 4 {
                    return Err(OutOfFragment::UnsupportedCommand("define-const".into()));
                }
                let (SExpr::Atom(name), SExpr::Atom(sort_name), val_expr) =
                    (&items[1], &items[2], &items[3])
                else {
                    return Err(OutOfFragment::UnsupportedCommand("define-const".into()));
                };
                if sort_name != "Int" {
                    return Err(OutOfFragment::UnsupportedSort(sort_name.clone()));
                }
                let k = eval_const_int(val_expr, &scope.defined_ints)
                    .ok_or_else(|| OutOfFragment::UnsupportedTerm("define-const non-literal".into()))?;
                scope.consts.insert(name.clone(), SmtSort::Int);
                scope.defined_ints.insert(name.clone(), k);
            }
            "declare-fun" => {
                if items.len() != 4 {
                    return Err(OutOfFragment::UnsupportedCommand("declare-fun".into()));
                }
                let (SExpr::Atom(name), SExpr::List(arg_sorts), SExpr::Atom(ret_name)) =
                    (&items[1], &items[2], &items[3])
                else {
                    return Err(OutOfFragment::UnsupportedCommand("declare-fun".into()));
                };
                let ret = SmtSort::parse(ret_name)
                    .ok_or_else(|| OutOfFragment::UnsupportedSort(ret_name.clone()))?;
                if arg_sorts.is_empty() {
                    if ret == SmtSort::Entity && !scope.entity_consts.contains(name) {
                        scope.entity_consts.push(name.clone());
                    }
                    scope.consts.insert(name.clone(), ret);
                } else {
                    if ret == SmtSort::Entity {
                        return Err(OutOfFragment::FunctionReturnsEntity(name.clone()));
                    }
                    let mut parsed_args = Vec::with_capacity(arg_sorts.len());
                    for a in arg_sorts {
                        let SExpr::Atom(aname) = a else {
                            return Err(OutOfFragment::UnsupportedSort("complex sort".into()));
                        };
                        let asort = SmtSort::parse(aname)
                            .ok_or_else(|| OutOfFragment::UnsupportedSort(aname.clone()))?;
                        if asort != SmtSort::Entity {
                            return Err(OutOfFragment::FunctionNonEntityArg(name.clone()));
                        }
                        parsed_args.push(asort);
                    }
                    scope.funs.insert(
                        name.clone(),
                        FunSig {
                            args: parsed_args,
                            ret,
                        },
                    );
                }
            }
            "push" => {
                stack.push(scope.clone());
            }
            "pop" => {
                if let Some(prev) = stack.pop() {
                    scope = prev;
                }
            }
            "assert" => {
                if items.len() != 2 {
                    return Err(OutOfFragment::UnsupportedCommand("assert".into()));
                }
                let mut has_q = false;
                let sort = check_term(
                    &items[1],
                    &scope,
                    &BTreeMap::new(),
                    &mut has_q,
                )?;
                if sort != SmtSort::Bool {
                    return Err(OutOfFragment::TypeMismatch("assert expects Bool".into()));
                }
                if has_q {
                    uses_entity_quantifier = true;
                }
            }
            "check-sat" | "get-model" => {}
            other => return Err(OutOfFragment::UnsupportedCommand(other.to_string())),
        }
    }

    // Second pass: emit the quantifier-free SMT-LIB2 script with every `forall ((x Entity))`
    // expanded over the active Entity constants (or `__entity_witness` if none were declared).
    let all_entity_consts = scope.entity_consts.clone();
    let mut out_lines = Vec::new();
    let mut declared_entities: BTreeSet<String> = BTreeSet::new();
    let mut active_entities: Vec<String> = all_entity_consts.clone();
    let mut injected_witness = false;

    for form in &forms {
        let SExpr::List(items) = form else {
            unreachable!();
        };
        let SExpr::Atom(cmd) = &items[0] else {
            unreachable!();
        };
        match cmd.as_str() {
            "declare-sort" => {
                out_lines.push(render_sexpr(form));
            }
            "declare-const" => {
                if let (SExpr::Atom(name), SExpr::Atom(sort_name)) = (&items[1], &items[2]) {
                    let sort = SmtSort::parse(sort_name).unwrap();
                    if sort == SmtSort::Entity {
                        if declared_entities.insert(name.clone()) {
                            out_lines.push(render_sexpr(form));
                        }
                        continue;
                    }
                }
                out_lines.push(render_sexpr(form));
            }
            "define-const" => {
                out_lines.push(render_sexpr(form));
            }
            "declare-fun" => {
                if let (SExpr::Atom(name), SExpr::List(arg_sorts), SExpr::Atom(ret_name)) =
                    (&items[1], &items[2], &items[3])
                {
                    let ret = SmtSort::parse(ret_name).unwrap();
                    if arg_sorts.is_empty() && ret == SmtSort::Entity {
                        if declared_entities.insert(name.clone()) {
                            out_lines.push(render_sexpr(form));
                        }
                        continue;
                    }
                }
                out_lines.push(render_sexpr(form));
            }
            "push" | "pop" => {
                out_lines.push(render_sexpr(form));
            }
            "assert" => {
                if uses_entity_quantifier {
                    if active_entities.is_empty() && !injected_witness {
                        let witness = "__entity_witness".to_string();
                        out_lines.push(format!("(declare-const {} Entity)", witness));
                        declared_entities.insert(witness.clone());
                        active_entities.push(witness);
                        injected_witness = true;
                    } else {
                        for ent in &all_entity_consts {
                            if declared_entities.insert(ent.clone()) {
                                out_lines.push(format!("(declare-const {} Entity)", ent));
                            }
                        }
                    }
                }
                let expanded =
                    expand_quantifiers(&items[1], &active_entities, &BTreeMap::new());
                out_lines.push(format!("(assert {})", render_sexpr(&expanded)));
            }
            _ => {
                out_lines.push(render_sexpr(form));
            }
        }
    }

    Ok(out_lines.join("\n") + "\n")
}

fn eval_const_int(expr: &SExpr, defined: &BTreeMap<String, i64>) -> Option<i64> {
    match expr {
        SExpr::Atom(a) => {
            if let Ok(n) = a.parse::<i64>() {
                Some(n)
            } else {
                defined.get(a).copied()
            }
        }
        SExpr::List(items) => match items.as_slice() {
            [SExpr::Atom(op), x] if op == "-" => eval_const_int(x, defined)?.checked_neg(),
            _ => None,
        },
    }
}

fn check_term(
    expr: &SExpr,
    scope: &Scope,
    locals: &BTreeMap<String, (SmtSort, Option<i64>)>,
    has_quantifier: &mut bool,
) -> Result<SmtSort, OutOfFragment> {
    match expr {
        SExpr::Atom(a) => {
            if a == "true" || a == "false" {
                return Ok(SmtSort::Bool);
            }
            if a.parse::<i64>().is_ok() {
                return Ok(SmtSort::Int);
            }
            if a.starts_with('"') {
                return Ok(SmtSort::String);
            }
            if let Some((sort, _)) = locals.get(a) {
                return Ok(*sort);
            }
            if let Some(sort) = scope.consts.get(a) {
                return Ok(*sort);
            }
            Err(OutOfFragment::UnknownSymbol(a.clone()))
        }
        SExpr::List(items) => {
            let Some(SExpr::Atom(head)) = items.first() else {
                return Err(OutOfFragment::UnsupportedTerm(render_sexpr(expr)));
            };
            match head.as_str() {
                "not" => {
                    if items.len() != 2 {
                        return Err(OutOfFragment::TypeMismatch("not arity".into()));
                    }
                    let s = check_term(&items[1], scope, locals, has_quantifier)?;
                    if s != SmtSort::Bool {
                        return Err(OutOfFragment::TypeMismatch("not expects Bool".into()));
                    }
                    Ok(SmtSort::Bool)
                }
                "and" | "or" | "=>" => {
                    if items.len() < 2 {
                        return Err(OutOfFragment::TypeMismatch(format!("{} arity", head)));
                    }
                    for arg in &items[1..] {
                        let s = check_term(arg, scope, locals, has_quantifier)?;
                        if s != SmtSort::Bool {
                            return Err(OutOfFragment::TypeMismatch(format!(
                                "{} expects Bool",
                                head
                            )));
                        }
                    }
                    Ok(SmtSort::Bool)
                }
                "=" | "distinct" => {
                    if items.len() != 3 {
                        return Err(OutOfFragment::TypeMismatch(format!("{} arity", head)));
                    }
                    let l = check_term(&items[1], scope, locals, has_quantifier)?;
                    let r = check_term(&items[2], scope, locals, has_quantifier)?;
                    if l != r {
                        return Err(OutOfFragment::TypeMismatch(format!(
                            "{} sort {:?} vs {:?}",
                            head, l, r
                        )));
                    }
                    Ok(SmtSort::Bool)
                }
                "<" | "<=" | ">" | ">=" => {
                    if items.len() != 3 {
                        return Err(OutOfFragment::TypeMismatch(format!("{} arity", head)));
                    }
                    let l = check_term(&items[1], scope, locals, has_quantifier)?;
                    let r = check_term(&items[2], scope, locals, has_quantifier)?;
                    if l != SmtSort::Int || r != SmtSort::Int {
                        return Err(OutOfFragment::TypeMismatch(format!(
                            "{} expects Int",
                            head
                        )));
                    }
                    Ok(SmtSort::Bool)
                }
                "+" | "-" => {
                    if items.len() < 2 {
                        return Err(OutOfFragment::TypeMismatch(format!("{} arity", head)));
                    }
                    for arg in &items[1..] {
                        let s = check_term(arg, scope, locals, has_quantifier)?;
                        if s != SmtSort::Int {
                            return Err(OutOfFragment::TypeMismatch(format!(
                                "{} expects Int",
                                head
                            )));
                        }
                    }
                    Ok(SmtSort::Int)
                }
                "abs" => {
                    if items.len() != 2 {
                        return Err(OutOfFragment::TypeMismatch("abs arity".into()));
                    }
                    let s = check_term(&items[1], scope, locals, has_quantifier)?;
                    if s != SmtSort::Int {
                        return Err(OutOfFragment::TypeMismatch("abs expects Int".into()));
                    }
                    Ok(SmtSort::Int)
                }
                "*" => {
                    if items.len() != 3 {
                        return Err(OutOfFragment::NonlinearMultiplication);
                    }
                    let l = check_term(&items[1], scope, locals, has_quantifier)?;
                    let r = check_term(&items[2], scope, locals, has_quantifier)?;
                    if l != SmtSort::Int || r != SmtSort::Int {
                        return Err(OutOfFragment::TypeMismatch("* expects Int".into()));
                    }
                    let l_const = is_const_int(&items[1], scope, locals);
                    let r_const = is_const_int(&items[2], scope, locals);
                    if l_const.is_none() && r_const.is_none() {
                        return Err(OutOfFragment::NonlinearMultiplication);
                    }
                    Ok(SmtSort::Int)
                }
                "div" | "mod" => {
                    if items.len() != 3 {
                        return Err(OutOfFragment::NonConstantDivMod);
                    }
                    let l = check_term(&items[1], scope, locals, has_quantifier)?;
                    let r = check_term(&items[2], scope, locals, has_quantifier)?;
                    if l != SmtSort::Int || r != SmtSort::Int {
                        return Err(OutOfFragment::TypeMismatch("div/mod expects Int".into()));
                    }
                    match is_const_int(&items[2], scope, locals) {
                        Some(d) if d > 0 => Ok(SmtSort::Int),
                        _ => Err(OutOfFragment::NonConstantDivMod),
                    }
                }
                "ite" => {
                    if items.len() != 4 {
                        return Err(OutOfFragment::TypeMismatch("ite arity".into()));
                    }
                    let c = check_term(&items[1], scope, locals, has_quantifier)?;
                    let t = check_term(&items[2], scope, locals, has_quantifier)?;
                    let e = check_term(&items[3], scope, locals, has_quantifier)?;
                    if c != SmtSort::Bool || t != e {
                        return Err(OutOfFragment::TypeMismatch("ite sort mismatch".into()));
                    }
                    Ok(t)
                }
                "let" => {
                    if items.len() != 3 {
                        return Err(OutOfFragment::TypeMismatch("let arity".into()));
                    }
                    let SExpr::List(bindings) = &items[1] else {
                        return Err(OutOfFragment::TypeMismatch("let bindings".into()));
                    };
                    let mut next_locals = locals.clone();
                    for b in bindings {
                        let SExpr::List(pair) = b else {
                            return Err(OutOfFragment::TypeMismatch("let pair".into()));
                        };
                        if pair.len() != 2 {
                            return Err(OutOfFragment::TypeMismatch("let pair len".into()));
                        }
                        let SExpr::Atom(vname) = &pair[0] else {
                            return Err(OutOfFragment::TypeMismatch("let var".into()));
                        };
                        let vsort = check_term(&pair[1], scope, locals, has_quantifier)?;
                        let vconst = is_const_int(&pair[1], scope, locals);
                        next_locals.insert(vname.clone(), (vsort, vconst));
                    }
                    check_term(&items[2], scope, &next_locals, has_quantifier)
                }
                "forall" => {
                    if items.len() != 3 {
                        return Err(OutOfFragment::QuantifierNotForallEntity("forall arity".into()));
                    }
                    let SExpr::List(binders) = &items[1] else {
                        return Err(OutOfFragment::QuantifierNotForallEntity("forall binders".into()));
                    };
                    if binders.is_empty() {
                        return Err(OutOfFragment::QuantifierNotForallEntity("empty forall".into()));
                    }
                    let mut next_locals = locals.clone();
                    for b in binders {
                        let SExpr::List(pair) = b else {
                            return Err(OutOfFragment::QuantifierNotForallEntity(render_sexpr(b)));
                        };
                        if pair.len() != 2 {
                            return Err(OutOfFragment::QuantifierNotForallEntity(render_sexpr(b)));
                        }
                        let (SExpr::Atom(vname), SExpr::Atom(sname)) = (&pair[0], &pair[1]) else {
                            return Err(OutOfFragment::QuantifierNotForallEntity(render_sexpr(b)));
                        };
                        if sname != "Entity" {
                            return Err(OutOfFragment::QuantifierNotForallEntity(format!(
                                "({} {})",
                                vname, sname
                            )));
                        }
                        next_locals.insert(vname.clone(), (SmtSort::Entity, None));
                    }
                    *has_quantifier = true;
                    let body_sort = check_term(&items[2], scope, &next_locals, has_quantifier)?;
                    if body_sort != SmtSort::Bool {
                        return Err(OutOfFragment::TypeMismatch("forall body must be Bool".into()));
                    }
                    Ok(SmtSort::Bool)
                }
                "exists" => Err(OutOfFragment::QuantifierNotForallEntity("exists".into())),
                other => {
                    let Some(sig) = scope.funs.get(other) else {
                        return Err(OutOfFragment::UnknownSymbol(other.to_string()));
                    };
                    if items.len() != 1 + sig.args.len() {
                        return Err(OutOfFragment::TypeMismatch(format!(
                            "application of `{}` arity",
                            other
                        )));
                    }
                    for (arg, expected) in items[1..].iter().zip(&sig.args) {
                        let actual = check_term(arg, scope, locals, has_quantifier)?;
                        if actual != *expected {
                            return Err(OutOfFragment::TypeMismatch(format!(
                                "argument to `{}` expected {:?}, got {:?}",
                                other, expected, actual
                            )));
                        }
                    }
                    Ok(sig.ret)
                }
            }
        }
    }
}

fn is_const_int(
    expr: &SExpr,
    scope: &Scope,
    locals: &BTreeMap<String, (SmtSort, Option<i64>)>,
) -> Option<i64> {
    if let Some(k) = eval_const_int(expr, &scope.defined_ints) {
        return Some(k);
    }
    if let SExpr::Atom(a) = expr {
        if let Some((_, Some(k))) = locals.get(a) {
            return Some(*k);
        }
    }
    None
}

fn expand_quantifiers(
    expr: &SExpr,
    entity_consts: &[String],
    subst: &BTreeMap<String, String>,
) -> SExpr {
    match expr {
        SExpr::Atom(a) => {
            if let Some(rep) = subst.get(a) {
                SExpr::Atom(rep.clone())
            } else {
                SExpr::Atom(a.clone())
            }
        }
        SExpr::List(items) => {
            if let Some(SExpr::Atom(head)) = items.first() {
                if head == "forall" && items.len() == 3 {
                    if let SExpr::List(binders) = &items[1] {
                        let vars: Vec<String> = binders
                            .iter()
                            .filter_map(|b| match b {
                                SExpr::List(pair) if pair.len() == 2 => match &pair[0] {
                                    SExpr::Atom(v) => Some(v.clone()),
                                    _ => None,
                                },
                                _ => None,
                            })
                            .collect();
                        let mut conjuncts = Vec::new();
                        instantiate_cartesian(&vars, 0, entity_consts, subst, &items[2], &mut conjuncts);
                        return match conjuncts.len() {
                            0 => SExpr::Atom("true".into()),
                            1 => conjuncts.into_iter().next().unwrap(),
                            _ => {
                                let mut list = Vec::with_capacity(1 + conjuncts.len());
                                list.push(SExpr::Atom("and".into()));
                                list.extend(conjuncts);
                                SExpr::List(list)
                            }
                        };
                    }
                } else if head == "let" && items.len() == 3 {
                    if let SExpr::List(bindings) = &items[1] {
                        let mut shadowed: BTreeSet<String> = BTreeSet::new();
                        let mut new_bindings = Vec::with_capacity(bindings.len());
                        for b in bindings {
                            if let SExpr::List(pair) = b {
                                if pair.len() == 2 {
                                    if let SExpr::Atom(v) = &pair[0] {
                                        shadowed.insert(v.clone());
                                        new_bindings.push(SExpr::List(vec![
                                            SExpr::Atom(v.clone()),
                                            expand_quantifiers(&pair[1], entity_consts, subst),
                                        ]));
                                    }
                                }
                            }
                        }
                        let mut inner_subst = subst.clone();
                        for v in shadowed {
                            inner_subst.remove(&v);
                        }
                        return SExpr::List(vec![
                            SExpr::Atom("let".into()),
                            SExpr::List(new_bindings),
                            expand_quantifiers(&items[2], entity_consts, &inner_subst),
                        ]);
                    }
                }
            }
            SExpr::List(
                items
                    .iter()
                    .map(|it| expand_quantifiers(it, entity_consts, subst))
                    .collect(),
            )
        }
    }
}

fn instantiate_cartesian(
    vars: &[String],
    idx: usize,
    entity_consts: &[String],
    current_subst: &BTreeMap<String, String>,
    body: &SExpr,
    out: &mut Vec<SExpr>,
) {
    if idx == vars.len() {
        out.push(expand_quantifiers(body, entity_consts, current_subst));
        return;
    }
    let v = &vars[idx];
    for c in entity_consts {
        let mut next_subst = current_subst.clone();
        next_subst.insert(v.clone(), c.clone());
        instantiate_cartesian(vars, idx + 1, entity_consts, &next_subst, body, out);
    }
}

fn render_sexpr(s: &SExpr) -> String {
    match s {
        SExpr::Atom(a) => a.clone(),
        SExpr::List(items) => {
            let parts: Vec<String> = items.iter().map(render_sexpr).collect();
            format!("({})", parts.join(" "))
        }
    }
}

// ============================================================================
// Decision Procedure for `bil-smt` (Roadmap 8.1.3)
// ============================================================================

/// Linear integer expression: `constant + sum_i coeffs[v_i] * x_{v_i}`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct LinExpr {
    coeffs: BTreeMap<usize, i128>,
    constant: i128,
}

impl LinExpr {
    fn from_const(c: i128) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    fn from_var(v: usize) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(v, 1);
        Self {
            coeffs,
            constant: 0,
        }
    }

    fn neg(&self) -> Option<Self> {
        let mut coeffs = BTreeMap::new();
        for (&v, &c) in &self.coeffs {
            coeffs.insert(v, c.checked_neg()?);
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_neg()?,
        })
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let mut coeffs = self.coeffs.clone();
        for (&v, &c) in &other.coeffs {
            let next = coeffs.get(&v).copied().unwrap_or(0).checked_add(c)?;
            if next == 0 {
                coeffs.remove(&v);
            } else {
                coeffs.insert(v, next);
            }
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    fn scale(&self, k: i128) -> Option<Self> {
        if k == 0 {
            return Some(Self::from_const(0));
        }
        let mut coeffs = BTreeMap::new();
        for (&v, &c) in &self.coeffs {
            let sc = c.checked_mul(k)?;
            if sc != 0 {
                coeffs.insert(v, sc);
            }
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_mul(k)?,
        })
    }
}

/// Canonical linear integer inequality: `sum_i a_i * x_i <= rhs`, with `gcd(|a_i|) == 1`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct LeqConstraint {
    coeffs: BTreeMap<usize, i128>,
    rhs: i128,
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

#[derive(Debug, Clone)]
enum NormLeq {
    AlwaysTrue,
    AlwaysFalse,
    Constraint(LeqConstraint),
}

/// Normalizes `expr <= 0` into `sum a_i x_i <= -constant` with GCD tightening.
fn normalize_leq_zero(expr: &LinExpr) -> Option<NormLeq> {
    let rhs = expr.constant.checked_neg()?;
    if expr.coeffs.is_empty() {
        return Some(if 0 <= rhs {
            NormLeq::AlwaysTrue
        } else {
            NormLeq::AlwaysFalse
        });
    }
    let mut g: u128 = 0;
    for &c in expr.coeffs.values() {
        g = gcd_u128(g, c.unsigned_abs());
    }
    let g_i128 = i128::try_from(g).ok()?;
    let mut coeffs = BTreeMap::new();
    for (&v, &c) in &expr.coeffs {
        if c != 0 {
            coeffs.insert(v, c / g_i128);
        }
    }
    let tightened_rhs = rhs.div_euclid(g_i128);
    Some(NormLeq::Constraint(LeqConstraint {
        coeffs,
        rhs: tightened_rhs,
    }))
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Formula {
    True,
    False,
    BoolVar(usize, bool),
    Leq(LeqConstraint),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
}

impl Formula {
    fn not(f: Formula) -> Formula {
        match f {
            Formula::True => Formula::False,
            Formula::False => Formula::True,
            Formula::BoolVar(v, pol) => Formula::BoolVar(v, !pol),
            Formula::Not(inner) => *inner,
            Formula::Leq(c) => {
                // !(sum a_i x_i <= rhs)  <=>  sum (-a_i) x_i <= -rhs - 1
                let mut neg_coeffs = BTreeMap::new();
                for (&v, &a) in &c.coeffs {
                    neg_coeffs.insert(v, -a);
                }
                Formula::Leq(LeqConstraint {
                    coeffs: neg_coeffs,
                    rhs: -c.rhs - 1,
                })
            }
            other => Formula::Not(Box::new(other)),
        }
    }

    fn and(items: Vec<Formula>) -> Formula {
        let mut flat = Vec::new();
        for it in items {
            match it {
                Formula::False => return Formula::False,
                Formula::True => {}
                Formula::And(sub) => flat.extend(sub),
                other => {
                    if !flat.contains(&other) {
                        flat.push(other);
                    }
                }
            }
        }
        match flat.len() {
            0 => Formula::True,
            1 => flat.into_iter().next().unwrap(),
            _ => Formula::And(flat),
        }
    }

    fn or(items: Vec<Formula>) -> Formula {
        let mut flat = Vec::new();
        for it in items {
            match it {
                Formula::True => return Formula::True,
                Formula::False => {}
                Formula::Or(sub) => flat.extend(sub),
                other => {
                    if !flat.contains(&other) {
                        flat.push(other);
                    }
                }
            }
        }
        match flat.len() {
            0 => Formula::False,
            1 => flat.into_iter().next().unwrap(),
            _ => Formula::Or(flat),
        }
    }

    fn implies(a: Formula, b: Formula) -> Formula {
        Formula::or(vec![Formula::not(a), b])
    }

    fn iff(a: Formula, b: Formula) -> Formula {
        Formula::and(vec![
            Formula::implies(a.clone(), b.clone()),
            Formula::implies(b, a),
        ])
    }
}

#[derive(Debug, Clone)]
enum LoweredTerm {
    Bool(Formula),
    Int(LinExpr),
}

struct LoweringCtx<'a> {
    scope: &'a Scope,
    entity_equality_used: bool,
    int_var_ids: BTreeMap<String, usize>,
    int_var_names: Vec<String>,
    bool_var_ids: BTreeMap<String, usize>,
    bool_var_names: Vec<String>,
    string_lit_ids: BTreeMap<String, i128>,
    string_vars: BTreeSet<usize>,
    entity_const_ids: BTreeMap<String, i128>,
    entity_vars: BTreeMap<String, usize>,
    uf_apps: BTreeMap<String, Vec<(Vec<LinExpr>, LoweredTerm)>>,
    ite_cache: BTreeMap<(Formula, LinExpr, LinExpr), usize>,
    abs_cache: BTreeMap<LinExpr, usize>,
    divmod_cache: BTreeMap<(LinExpr, i128), (usize, usize)>,
    side_constraints: Vec<Formula>,
}

impl<'a> LoweringCtx<'a> {
    fn new(scope: &'a Scope, entity_equality_used: bool) -> Self {
        let mut entity_const_ids = BTreeMap::new();
        for (idx, name) in scope.entity_consts.iter().enumerate() {
            entity_const_ids.insert(name.clone(), idx as i128);
        }
        Self {
            scope,
            entity_equality_used,
            int_var_ids: BTreeMap::new(),
            int_var_names: Vec::new(),
            bool_var_ids: BTreeMap::new(),
            bool_var_names: Vec::new(),
            string_lit_ids: BTreeMap::new(),
            string_vars: BTreeSet::new(),
            entity_const_ids,
            entity_vars: BTreeMap::new(),
            uf_apps: BTreeMap::new(),
            ite_cache: BTreeMap::new(),
            abs_cache: BTreeMap::new(),
            divmod_cache: BTreeMap::new(),
            side_constraints: Vec::new(),
        }
    }

    fn get_or_alloc_int_var(&mut self, name: &str) -> usize {
        if let Some(&id) = self.int_var_ids.get(name) {
            return id;
        }
        let id = self.int_var_names.len();
        self.int_var_names.push(name.to_string());
        self.int_var_ids.insert(name.to_string(), id);
        id
    }

    fn fresh_int_var(&mut self, prefix: &str) -> usize {
        let name = format!("__{}_{}", prefix, self.int_var_names.len());
        self.get_or_alloc_int_var(&name)
    }

    fn get_or_alloc_bool_var(&mut self, name: &str) -> usize {
        if let Some(&id) = self.bool_var_ids.get(name) {
            return id;
        }
        let id = self.bool_var_names.len();
        self.bool_var_names.push(name.to_string());
        self.bool_var_ids.insert(name.to_string(), id);
        id
    }

    fn fresh_bool_var(&mut self, prefix: &str) -> usize {
        let name = format!("__{}_{}", prefix, self.bool_var_names.len());
        self.get_or_alloc_bool_var(&name)
    }

    fn make_leq_zero(&self, expr: &LinExpr) -> Option<Formula> {
        Some(match normalize_leq_zero(expr)? {
            NormLeq::AlwaysTrue => Formula::True,
            NormLeq::AlwaysFalse => Formula::False,
            NormLeq::Constraint(c) => Formula::Leq(c),
        })
    }

    fn make_leq(&self, lhs: &LinExpr, rhs: &LinExpr) -> Option<Formula> {
        let diff = lhs.sub(rhs)?;
        self.make_leq_zero(&diff)
    }

    fn make_lt(&self, lhs: &LinExpr, rhs: &LinExpr) -> Option<Formula> {
        // lhs < rhs  <=>  lhs - rhs + 1 <= 0
        let diff = lhs.sub(rhs)?.add(&LinExpr::from_const(1))?;
        self.make_leq_zero(&diff)
    }

    fn make_eq_int(&self, lhs: &LinExpr, rhs: &LinExpr) -> Option<Formula> {
        Some(Formula::and(vec![
            self.make_leq(lhs, rhs)?,
            self.make_leq(rhs, lhs)?,
        ]))
    }

    fn lower_entity_const(&mut self, name: &str) -> LinExpr {
        if self.entity_equality_used {
            let v = self.get_or_alloc_int_var(&format!("__ent_{}", name));
            if !self.entity_vars.contains_key(name) {
                self.entity_vars.insert(name.to_string(), v);
                let max_e = (self.scope.entity_consts.len().saturating_sub(1)) as i128;
                let ve = LinExpr::from_var(v);
                if let Some(f_lo) = self.make_leq(&LinExpr::from_const(0), &ve) {
                    self.side_constraints.push(f_lo);
                }
                if let Some(f_hi) = self.make_leq(&ve, &LinExpr::from_const(max_e)) {
                    self.side_constraints.push(f_hi);
                }
            }
            LinExpr::from_var(v)
        } else {
            let id = self.entity_const_ids.get(name).copied().unwrap_or(0);
            LinExpr::from_const(id)
        }
    }

    fn lower_term(
        &mut self,
        expr: &SExpr,
        locals: &BTreeMap<String, LoweredTerm>,
    ) -> Option<LoweredTerm> {
        match expr {
            SExpr::Atom(a) => {
                if a == "true" {
                    return Some(LoweredTerm::Bool(Formula::True));
                }
                if a == "false" {
                    return Some(LoweredTerm::Bool(Formula::False));
                }
                if let Ok(n) = a.parse::<i64>() {
                    return Some(LoweredTerm::Int(LinExpr::from_const(i128::from(n))));
                }
                if a.starts_with('"') {
                    let next_id = self.string_lit_ids.len() as i128;
                    let id = *self.string_lit_ids.entry(a.clone()).or_insert(next_id);
                    return Some(LoweredTerm::Int(LinExpr::from_const(id)));
                }
                if let Some(bound) = locals.get(a) {
                    return Some(bound.clone());
                }
                if let Some(&k) = self.scope.defined_ints.get(a) {
                    return Some(LoweredTerm::Int(LinExpr::from_const(i128::from(k))));
                }
                match self.scope.consts.get(a)? {
                    SmtSort::Bool => {
                        let v = self.get_or_alloc_bool_var(a);
                        Some(LoweredTerm::Bool(Formula::BoolVar(v, true)))
                    }
                    SmtSort::Int => {
                        let v = self.get_or_alloc_int_var(a);
                        Some(LoweredTerm::Int(LinExpr::from_var(v)))
                    }
                    SmtSort::String => {
                        let v = self.get_or_alloc_int_var(a);
                        if self.string_vars.insert(v) {
                            let ve = LinExpr::from_var(v);
                            let f_lo = self.make_leq(&LinExpr::from_const(0), &ve)?;
                            self.side_constraints.push(f_lo);
                        }
                        Some(LoweredTerm::Int(LinExpr::from_var(v)))
                    }
                    SmtSort::Entity => Some(LoweredTerm::Int(self.lower_entity_const(a))),
                }
            }
            SExpr::List(items) => {
                let SExpr::Atom(head) = items.first()? else {
                    return None;
                };
                match head.as_str() {
                    "not" => {
                        let LoweredTerm::Bool(f) = self.lower_term(&items[1], locals)? else {
                            return None;
                        };
                        Some(LoweredTerm::Bool(Formula::not(f)))
                    }
                    "and" => {
                        let mut fs = Vec::with_capacity(items.len() - 1);
                        for arg in &items[1..] {
                            let LoweredTerm::Bool(f) = self.lower_term(arg, locals)? else {
                                return None;
                            };
                            fs.push(f);
                        }
                        Some(LoweredTerm::Bool(Formula::and(fs)))
                    }
                    "or" => {
                        let mut fs = Vec::with_capacity(items.len() - 1);
                        for arg in &items[1..] {
                            let LoweredTerm::Bool(f) = self.lower_term(arg, locals)? else {
                                return None;
                            };
                            fs.push(f);
                        }
                        Some(LoweredTerm::Bool(Formula::or(fs)))
                    }
                    "=>" => {
                        let mut fs = Vec::with_capacity(items.len() - 1);
                        for arg in &items[1..] {
                            let LoweredTerm::Bool(f) = self.lower_term(arg, locals)? else {
                                return None;
                            };
                            fs.push(f);
                        }
                        let mut acc = fs.pop()?;
                        while let Some(prev) = fs.pop() {
                            acc = Formula::implies(prev, acc);
                        }
                        Some(LoweredTerm::Bool(acc))
                    }
                    "=" | "distinct" => {
                        let l = self.lower_term(&items[1], locals)?;
                        let r = self.lower_term(&items[2], locals)?;
                        let eq_f = match (l, r) {
                            (LoweredTerm::Bool(fb1), LoweredTerm::Bool(fb2)) => {
                                Formula::iff(fb1, fb2)
                            }
                            (LoweredTerm::Int(le1), LoweredTerm::Int(le2)) => {
                                self.make_eq_int(&le1, &le2)?
                            }
                            _ => return None,
                        };
                        let res = if head == "=" {
                            eq_f
                        } else {
                            Formula::not(eq_f)
                        };
                        Some(LoweredTerm::Bool(res))
                    }
                    "<" | "<=" | ">" | ">=" => {
                        let LoweredTerm::Int(l) = self.lower_term(&items[1], locals)? else {
                            return None;
                        };
                        let LoweredTerm::Int(r) = self.lower_term(&items[2], locals)? else {
                            return None;
                        };
                        let f = match head.as_str() {
                            "<=" => self.make_leq(&l, &r)?,
                            "<" => self.make_lt(&l, &r)?,
                            ">=" => self.make_leq(&r, &l)?,
                            ">" => self.make_lt(&r, &l)?,
                            _ => unreachable!(),
                        };
                        Some(LoweredTerm::Bool(f))
                    }
                    "+" => {
                        let mut acc = LinExpr::from_const(0);
                        for arg in &items[1..] {
                            let LoweredTerm::Int(le) = self.lower_term(arg, locals)? else {
                                return None;
                            };
                            acc = acc.add(&le)?;
                        }
                        Some(LoweredTerm::Int(acc))
                    }
                    "-" => {
                        if items.len() == 2 {
                            let LoweredTerm::Int(le) = self.lower_term(&items[1], locals)? else {
                                return None;
                            };
                            Some(LoweredTerm::Int(le.neg()?))
                        } else {
                            let LoweredTerm::Int(mut acc) =
                                self.lower_term(&items[1], locals)?
                            else {
                                return None;
                            };
                            for arg in &items[2..] {
                                let LoweredTerm::Int(le) = self.lower_term(arg, locals)? else {
                                    return None;
                                };
                                acc = acc.sub(&le)?;
                            }
                            Some(LoweredTerm::Int(acc))
                        }
                    }
                    "*" => {
                        let LoweredTerm::Int(l) = self.lower_term(&items[1], locals)? else {
                            return None;
                        };
                        let LoweredTerm::Int(r) = self.lower_term(&items[2], locals)? else {
                            return None;
                        };
                        if l.coeffs.is_empty() {
                            Some(LoweredTerm::Int(r.scale(l.constant)?))
                        } else if r.coeffs.is_empty() {
                            Some(LoweredTerm::Int(l.scale(r.constant)?))
                        } else {
                            None
                        }
                    }
                    "abs" => {
                        let LoweredTerm::Int(e) = self.lower_term(&items[1], locals)? else {
                            return None;
                        };
                        if e.coeffs.is_empty() {
                            return Some(LoweredTerm::Int(LinExpr::from_const(
                                e.constant.checked_abs()?,
                            )));
                        }
                        if let Some(&v) = self.abs_cache.get(&e) {
                            return Some(LoweredTerm::Int(LinExpr::from_var(v)));
                        }
                        let v = self.fresh_int_var("abs");
                        self.abs_cache.insert(e.clone(), v);
                        let ve = LinExpr::from_var(v);
                        let zero = LinExpr::from_const(0);
                        let neg_e = e.neg()?;
                        // v >= 0
                        let f_nonneg = self.make_leq(&zero, &ve)?;
                        // e >= 0 => v == e
                        let cond_pos = self.make_leq(&zero, &e)?;
                        let eq_pos = self.make_eq_int(&ve, &e)?;
                        // e < 0 => v == -e
                        let cond_neg = self.make_lt(&e, &zero)?;
                        let eq_neg = self.make_eq_int(&ve, &neg_e)?;
                        self.side_constraints.push(f_nonneg);
                        self.side_constraints
                            .push(Formula::implies(cond_pos, eq_pos));
                        self.side_constraints
                            .push(Formula::implies(cond_neg, eq_neg));
                        Some(LoweredTerm::Int(ve))
                    }
                    "div" | "mod" => {
                        let LoweredTerm::Int(e) = self.lower_term(&items[1], locals)? else {
                            return None;
                        };
                        let LoweredTerm::Int(d_expr) = self.lower_term(&items[2], locals)? else {
                            return None;
                        };
                        if !d_expr.coeffs.is_empty() || d_expr.constant <= 0 {
                            return None;
                        }
                        let d = d_expr.constant;
                        if e.coeffs.is_empty() {
                            let val = if head == "div" {
                                e.constant.div_euclid(d)
                            } else {
                                e.constant.rem_euclid(d)
                            };
                            return Some(LoweredTerm::Int(LinExpr::from_const(val)));
                        }
                        let (q, r) = if let Some(&pair) = self.divmod_cache.get(&(e.clone(), d)) {
                            pair
                        } else {
                            let q = self.fresh_int_var("div_q");
                            let r = self.fresh_int_var("mod_r");
                            self.divmod_cache.insert((e.clone(), d), (q, r));
                            let qe = LinExpr::from_var(q);
                            let re = LinExpr::from_var(r);
                            // e == d * q + r
                            let dq_plus_r = qe.scale(d)?.add(&re)?;
                            let eq_divmod = self.make_eq_int(&e, &dq_plus_r)?;
                            let r_ge_0 = self.make_leq(&LinExpr::from_const(0), &re)?;
                            let r_le_d1 = self.make_leq(&re, &LinExpr::from_const(d - 1))?;
                            self.side_constraints.push(eq_divmod);
                            self.side_constraints.push(r_ge_0);
                            self.side_constraints.push(r_le_d1);
                            (q, r)
                        };
                        if head == "div" {
                            Some(LoweredTerm::Int(LinExpr::from_var(q)))
                        } else {
                            Some(LoweredTerm::Int(LinExpr::from_var(r)))
                        }
                    }
                    "ite" => {
                        let LoweredTerm::Bool(cond) = self.lower_term(&items[1], locals)? else {
                            return None;
                        };
                        let t_branch = self.lower_term(&items[2], locals)?;
                        let e_branch = self.lower_term(&items[3], locals)?;
                        match (t_branch, e_branch) {
                            (LoweredTerm::Bool(tb), LoweredTerm::Bool(eb)) => {
                                Some(LoweredTerm::Bool(Formula::and(vec![
                                    Formula::implies(cond.clone(), tb),
                                    Formula::implies(Formula::not(cond), eb),
                                ])))
                            }
                            (LoweredTerm::Int(ti), LoweredTerm::Int(ei)) => {
                                if ti == ei {
                                    return Some(LoweredTerm::Int(ti));
                                }
                                let key = (cond.clone(), ti.clone(), ei.clone());
                                if let Some(&v) = self.ite_cache.get(&key) {
                                    return Some(LoweredTerm::Int(LinExpr::from_var(v)));
                                }
                                let v = self.fresh_int_var("ite");
                                self.ite_cache.insert(key, v);
                                let ve = LinExpr::from_var(v);
                                let eq_t = self.make_eq_int(&ve, &ti)?;
                                let eq_e = self.make_eq_int(&ve, &ei)?;
                                self.side_constraints
                                    .push(Formula::implies(cond.clone(), eq_t));
                                self.side_constraints
                                    .push(Formula::implies(Formula::not(cond), eq_e));
                                Some(LoweredTerm::Int(ve))
                            }
                            _ => None,
                        }
                    }
                    "let" => {
                        let SExpr::List(bindings) = &items[1] else {
                            return None;
                        };
                        let mut next_locals = locals.clone();
                        for b in bindings {
                            let SExpr::List(pair) = b else {
                                return None;
                            };
                            let SExpr::Atom(vname) = &pair[0] else {
                                return None;
                            };
                            let val = self.lower_term(&pair[1], locals)?;
                            next_locals.insert(vname.clone(), val);
                        }
                        self.lower_term(&items[2], &next_locals)
                    }
                    other => {
                        let sig = self.scope.funs.get(other)?.clone();
                        let mut arg_exprs = Vec::with_capacity(sig.args.len());
                        for a in &items[1..] {
                            let LoweredTerm::Int(le) = self.lower_term(a, locals)? else {
                                return None;
                            };
                            arg_exprs.push(le);
                        }
                        if let Some(existing_list) = self.uf_apps.get(other) {
                            for (prev_args, prev_term) in existing_list {
                                if *prev_args == arg_exprs {
                                    return Some(prev_term.clone());
                                }
                            }
                        }
                        let fresh_term = match sig.ret {
                            SmtSort::Bool => {
                                let b = self.fresh_bool_var(&format!("uf_{}", other));
                                LoweredTerm::Bool(Formula::BoolVar(b, true))
                            }
                            SmtSort::Int => {
                                let v = self.fresh_int_var(&format!("uf_{}", other));
                                LoweredTerm::Int(LinExpr::from_var(v))
                            }
                            SmtSort::String => {
                                let v = self.fresh_int_var(&format!("uf_str_{}", other));
                                let ve = LinExpr::from_var(v);
                                let f_lo = self.make_leq(&LinExpr::from_const(0), &ve)?;
                                self.side_constraints.push(f_lo);
                                LoweredTerm::Int(ve)
                            }
                            SmtSort::Entity => return None,
                        };
                        // Add Ackermann congruence axioms against previous applications of `other`
                        // whenever arguments are not provably distinct constants.
                        let prev_entries =
                            self.uf_apps.get(other).cloned().unwrap_or_default();
                        for (prev_args, prev_term) in prev_entries {
                            let mut definitely_distinct = false;
                            let mut arg_eqs = Vec::with_capacity(arg_exprs.len());
                            for (a1, a2) in arg_exprs.iter().zip(prev_args.iter()) {
                                if a1.coeffs.is_empty()
                                    && a2.coeffs.is_empty()
                                    && a1.constant != a2.constant
                                {
                                    definitely_distinct = true;
                                    break;
                                }
                                arg_eqs.push(self.make_eq_int(a1, a2)?);
                            }
                            if !definitely_distinct {
                                let premise = Formula::and(arg_eqs);
                                let concl = match (&fresh_term, &prev_term) {
                                    (LoweredTerm::Bool(b1), LoweredTerm::Bool(b2)) => {
                                        Formula::iff(b1.clone(), b2.clone())
                                    }
                                    (LoweredTerm::Int(i1), LoweredTerm::Int(i2)) => {
                                        self.make_eq_int(i1, i2)?
                                    }
                                    _ => return None,
                                };
                                self.side_constraints
                                    .push(Formula::implies(premise, concl));
                            }
                        }
                        self.uf_apps
                            .entry(other.to_string())
                            .or_default()
                            .push((arg_exprs, fresh_term.clone()));
                        Some(fresh_term)
                    }
                }
            }
        }
    }
}

fn expr_uses_entity_equality_or_ite(
    expr: &SExpr,
    scope: &Scope,
    locals: &BTreeMap<String, SmtSort>,
) -> bool {
    let SExpr::List(items) = expr else {
        return false;
    };
    let Some(SExpr::Atom(head)) = items.first() else {
        return false;
    };
    if (head == "=" || head == "distinct")
        && items.len() == 3
        && infer_sort_quick(&items[1], scope, locals) == Some(SmtSort::Entity)
    {
        return true;
    }
    if head == "ite"
        && items.len() == 4
        && infer_sort_quick(&items[2], scope, locals) == Some(SmtSort::Entity)
    {
        return true;
    }
    if head == "let" && items.len() == 3 {
        if let SExpr::List(bindings) = &items[1] {
            let mut next_locals = locals.clone();
            for b in bindings {
                if let SExpr::List(pair) = b {
                    if pair.len() == 2 {
                        if let SExpr::Atom(v) = &pair[0] {
                            if expr_uses_entity_equality_or_ite(&pair[1], scope, locals) {
                                return true;
                            }
                            if let Some(s) = infer_sort_quick(&pair[1], scope, locals) {
                                next_locals.insert(v.clone(), s);
                            }
                        }
                    }
                }
            }
            return expr_uses_entity_equality_or_ite(&items[2], scope, &next_locals);
        }
    }
    items[1..]
        .iter()
        .any(|sub| expr_uses_entity_equality_or_ite(sub, scope, locals))
}

fn infer_sort_quick(
    expr: &SExpr,
    scope: &Scope,
    locals: &BTreeMap<String, SmtSort>,
) -> Option<SmtSort> {
    match expr {
        SExpr::Atom(a) => {
            if a == "true" || a == "false" {
                Some(SmtSort::Bool)
            } else if a.parse::<i64>().is_ok() {
                Some(SmtSort::Int)
            } else if a.starts_with('"') {
                Some(SmtSort::String)
            } else if let Some(&s) = locals.get(a) {
                Some(s)
            } else {
                scope.consts.get(a).copied()
            }
        }
        SExpr::List(items) => {
            let SExpr::Atom(head) = items.first()? else {
                return None;
            };
            match head.as_str() {
                "not" | "and" | "or" | "=>" | "=" | "distinct" | "<" | "<=" | ">" | ">="
                | "forall" => Some(SmtSort::Bool),
                "+" | "-" | "*" | "div" | "mod" | "abs" => Some(SmtSort::Int),
                "ite" if items.len() == 4 => infer_sort_quick(&items[2], scope, locals),
                "let" if items.len() == 3 => {
                    let SExpr::List(bindings) = &items[1] else {
                        return None;
                    };
                    let mut next_locals = locals.clone();
                    for b in bindings {
                        if let SExpr::List(pair) = b {
                            if pair.len() == 2 {
                                if let SExpr::Atom(v) = &pair[0] {
                                    if let Some(s) = infer_sort_quick(&pair[1], scope, locals) {
                                        next_locals.insert(v.clone(), s);
                                    }
                                }
                            }
                        }
                    }
                    infer_sort_quick(&items[2], scope, &next_locals)
                }
                other => scope.funs.get(other).map(|sig| sig.ret),
            }
        }
    }
}

// ============================================================================
// Exact QF_LIA + Boolean DPLL(T) Solver
// ============================================================================

const MAX_SOLVER_STEPS: usize = 200_000;
const MAX_INEQUALITIES_PER_STEP: usize = 2_048;

#[derive(Debug, Clone)]
enum LiaResult {
    Sat(Vec<i128>),
    Unsat,
    Unknown,
}

#[derive(Debug, Clone)]
enum EliminationStep {
    Assigned(usize, i128),
    Defined {
        var: usize,
        denom: i128,
        rest: BTreeMap<usize, i128>,
        rhs: i128,
    },
    FourierMotzkin {
        var: usize,
        lower: Vec<(i128, BTreeMap<usize, i128>, i128)>,
        upper: Vec<(i128, BTreeMap<usize, i128>, i128)>,
    },
}

fn ceil_div_i128(num: i128, den: i128) -> i128 {
    debug_assert!(den > 0);
    let q = num.div_euclid(den);
    let r = num.rem_euclid(den);
    if r == 0 {
        q
    } else {
        q + 1
    }
}

/// Solves a conjunction of `LeqConstraint`s over `num_vars` integer variables (`0..num_vars`),
/// returning an exact integer assignment `Vec<i128>` when satisfiable.
fn solve_qf_lia(
    constraints: &[LeqConstraint],
    num_vars: usize,
    steps: &mut usize,
) -> LiaResult {
    solve_qf_lia_inner(constraints, num_vars, steps, 0)
}

fn solve_qf_lia_inner(
    constraints: &[LeqConstraint],
    num_vars: usize,
    steps: &mut usize,
    depth: usize,
) -> LiaResult {
    if depth > 16 {
        return LiaResult::Unknown;
    }
    let mut active: BTreeSet<LeqConstraint> = constraints.iter().cloned().collect();
    let mut history: Vec<EliminationStep> = Vec::new();
    let mut eliminated: BTreeSet<usize> = BTreeSet::new();

    loop {
        *steps += 1;
        if *steps > MAX_SOLVER_STEPS || active.len() > MAX_INEQUALITIES_PER_STEP {
            return LiaResult::Unknown;
        }

        // 1. Bound propagation & single-variable interval tightening
        let mut bounds: BTreeMap<usize, (i128, i128)> = BTreeMap::new();
        let mut changed_bounds = true;
        while changed_bounds {
            changed_bounds = false;
            for c in &active {
                if c.coeffs.is_empty() {
                    if 0 > c.rhs {
                        return LiaResult::Unsat;
                    }
                    continue;
                }
                if c.coeffs.len() == 1 {
                    let (&v, &a) = c.coeffs.iter().next().unwrap();
                    let entry = bounds.entry(v).or_insert((i128::MIN / 4, i128::MAX / 4));
                    if a > 0 {
                        // a * v <= rhs  =>  v <= floor(rhs / a)
                        let ub = c.rhs.div_euclid(a);
                        if ub < entry.1 {
                            entry.1 = ub;
                            changed_bounds = true;
                        }
                    } else {
                        // (-|a|) * v <= rhs  =>  |a| * v >= -rhs  =>  v >= ceil(-rhs / |a|)
                        let Some(neg_rhs) = c.rhs.checked_neg() else {
                            return LiaResult::Unknown;
                        };
                        let Some(abs_a) = a.checked_neg() else {
                            return LiaResult::Unknown;
                        };
                        let lb = ceil_div_i128(neg_rhs, abs_a);
                        if lb > entry.0 {
                            entry.0 = lb;
                            changed_bounds = true;
                        }
                    }
                    if entry.0 > entry.1 {
                        return LiaResult::Unsat;
                    }
                }
            }
        }

        // 2. If any variable has a fixed value (lb == ub), substitute it out immediately
        let fixed_var = bounds
            .iter()
            .find(|(&v, &(lb, ub))| lb == ub && !eliminated.contains(&v))
            .map(|(&v, &(val, _))| (v, val));
        if let Some((v, val)) = fixed_var {
            eliminated.insert(v);
            history.push(EliminationStep::Assigned(v, val));
            let Some(next_active) = substitute_var(&active, v, val) else {
                return LiaResult::Unknown;
            };
            match next_active {
                Ok(set) => {
                    active = set;
                    continue;
                }
                Err(()) => return LiaResult::Unsat,
            }
        }

        // 2b. Equality detection: if active contains both `c <= rhs` and `-c <= -rhs`,
        // eliminate one variable from the equation (preferring a variable with `|a| == 1`).
        let mut found_eq: Option<(usize, i128, BTreeMap<usize, i128>, i128)> = None;
        for c in &active {
            if c.coeffs.len() < 2 {
                continue;
            }
            let mut neg_coeffs = BTreeMap::new();
            let mut ok = true;
            for (&u, &a) in &c.coeffs {
                if let Some(na) = a.checked_neg() {
                    neg_coeffs.insert(u, na);
                } else {
                    ok = false;
                    break;
                }
            }
            let Some(neg_rhs) = c.rhs.checked_neg() else {
                continue;
            };
            if !ok {
                continue;
            }
            let twin = LeqConstraint {
                coeffs: neg_coeffs,
                rhs: neg_rhs,
            };
            if active.contains(&twin) {
                // Pick variable in `c` with smallest `|a|`
                let (&best_u, &best_a) = c
                    .coeffs
                    .iter()
                    .min_by_key(|(_, &a)| a.unsigned_abs())
                    .unwrap();
                let mut rest = c.coeffs.clone();
                rest.remove(&best_u);
                found_eq = Some((best_u, best_a, rest, c.rhs));
                break;
            }
        }
        if let Some((eq_v, eq_a, eq_rest, eq_rhs)) = found_eq {
            let Some(next_active) =
                substitute_linear_eq(&active, eq_v, eq_a, &eq_rest, eq_rhs)
            else {
                return LiaResult::Unknown;
            };
            match next_active {
                Ok(set) => {
                    eliminated.insert(eq_v);
                    history.push(EliminationStep::Defined {
                        var: eq_v,
                        denom: eq_a,
                        rest: eq_rest,
                        rhs: eq_rhs,
                    });
                    active = set;
                    continue;
                }
                Err(()) => return LiaResult::Unsat,
            }
        }

        // Collect remaining variables present in active constraints
        let mut remaining_vars: BTreeSet<usize> = BTreeSet::new();
        for c in &active {
            for &v in c.coeffs.keys() {
                if !eliminated.contains(&v) {
                    remaining_vars.insert(v);
                }
            }
        }
        if remaining_vars.is_empty() {
            break;
        }

        // Pick variable to eliminate: prefer a variable with unit coefficient (`|a| == 1`) on all
        // lower bounds or all upper bounds (exact Fourier-Motzkin without dark shadow), minimizing
        // `pos_count * neg_count`.
        let mut best_var: Option<(usize, bool, usize, i128)> = None;
        for &v in &remaining_vars {
            let mut pos_count = 0usize;
            let mut neg_count = 0usize;
            let mut max_pos_coeff = 1i128;
            let mut max_neg_coeff = 1i128;
            for c in &active {
                if let Some(&a) = c.coeffs.get(&v) {
                    if a > 0 {
                        pos_count += 1;
                        if a > max_pos_coeff {
                            max_pos_coeff = a;
                        }
                    } else if a < 0 {
                        neg_count += 1;
                        let abs_a = -a;
                        if abs_a > max_neg_coeff {
                            max_neg_coeff = abs_a;
                        }
                    }
                }
            }
            let exact = max_pos_coeff == 1 || max_neg_coeff == 1 || pos_count == 0 || neg_count == 0;
            let prod = pos_count.saturating_mul(neg_count);
            let min_max_coeff = max_pos_coeff.min(max_neg_coeff);
            match best_var {
                None => best_var = Some((v, exact, prod, min_max_coeff)),
                Some((_, best_exact, best_prod, best_coeff)) => {
                    if (exact && !best_exact)
                        || (exact == best_exact
                            && (prod, min_max_coeff) < (best_prod, best_coeff))
                    {
                        best_var = Some((v, exact, prod, min_max_coeff));
                    }
                }
            }
        }

        let (elim_v, _, _, _) = best_var.unwrap();
        let mut upper = Vec::new();
        let mut lower = Vec::new();
        let mut others = BTreeSet::new();

        for c in &active {
            match c.coeffs.get(&elim_v).copied() {
                Some(a) if a > 0 => {
                    let mut rest = c.coeffs.clone();
                    rest.remove(&elim_v);
                    upper.push((a, rest, c.rhs));
                }
                Some(a) if a < 0 => {
                    let mut rest = c.coeffs.clone();
                    rest.remove(&elim_v);
                    lower.push((-a, rest, c.rhs));
                }
                _ => {
                    others.insert(c.clone());
                }
            }
        }

        // Combine every lower bound `(-a_l)*v + rest_l <= rhs_l` (`a_l * v >= -rhs_l + rest_l`)
        // with every upper bound `a_u*v + rest_u <= rhs_u`:
        // `a_u * rest_l + a_l * rest_u <= a_u * rhs_l + a_l * rhs_u`.
        for (a_l, rest_l, rhs_l) in &lower {
            for (a_u, rest_u, rhs_u) in &upper {
                let mut comb_coeffs = BTreeMap::new();
                for (&v, &c_l) in rest_l {
                    let Some(term) = a_u.checked_mul(c_l) else {
                        return LiaResult::Unknown;
                    };
                    if term != 0 {
                        comb_coeffs.insert(v, term);
                    }
                }
                for (&v, &c_u) in rest_u {
                    let Some(term) = a_l.checked_mul(c_u) else {
                        return LiaResult::Unknown;
                    };
                    let prev = comb_coeffs.get(&v).copied().unwrap_or(0);
                    let Some(sum) = prev.checked_add(term) else {
                        return LiaResult::Unknown;
                    };
                    if sum == 0 {
                        comb_coeffs.remove(&v);
                    } else {
                        comb_coeffs.insert(v, sum);
                    }
                }
                let Some(t1) = a_u.checked_mul(*rhs_l) else {
                    return LiaResult::Unknown;
                };
                let Some(t2) = a_l.checked_mul(*rhs_u) else {
                    return LiaResult::Unknown;
                };
                let Some(comb_rhs) = t1.checked_add(t2) else {
                    return LiaResult::Unknown;
                };
                let Some(neg_rhs) = comb_rhs.checked_neg() else {
                    return LiaResult::Unknown;
                };
                let lin = LinExpr {
                    coeffs: comb_coeffs,
                    constant: neg_rhs,
                };
                let Some(norm) = normalize_leq_zero(&lin) else {
                    return LiaResult::Unknown;
                };
                match norm {
                    NormLeq::AlwaysTrue => {}
                    NormLeq::AlwaysFalse => return LiaResult::Unsat,
                    NormLeq::Constraint(nc) => {
                        others.insert(nc);
                    }
                }
            }
        }

        eliminated.insert(elim_v);
        history.push(EliminationStep::FourierMotzkin {
            var: elim_v,
            lower,
            upper,
        });
        active = others;
    }

    let mut model = vec![0i128; num_vars];

    // Reconstruct eliminated variables in reverse order
    for step in history.into_iter().rev() {
        match step {
            EliminationStep::Assigned(v, val) => {
                model[v] = val;
            }
            EliminationStep::Defined {
                var,
                denom,
                rest,
                rhs,
            } => {
                // denom * var + sum(rest) == rhs  =>  denom * var == rhs - sum(rest)
                let mut sum_rest = 0i128;
                for (&u, &c) in &rest {
                    let Some(prod) = c.checked_mul(model[u]) else {
                        return LiaResult::Unknown;
                    };
                    let Some(next) = sum_rest.checked_add(prod) else {
                        return LiaResult::Unknown;
                    };
                    sum_rest = next;
                }
                let Some(num) = rhs.checked_sub(sum_rest) else {
                    return LiaResult::Unknown;
                };
                if num % denom != 0 {
                    return LiaResult::Unsat;
                }
                model[var] = num / denom;
            }
            EliminationStep::FourierMotzkin { var, lower, upper } => {
                let mut lb = i128::MIN / 4;
                let mut ub = i128::MAX / 4;
                for (a_l, rest_l, rhs_l) in &lower {
                    // -a_l * var + sum(rest_l) <= rhs_l  <=>  a_l * var >= sum(rest_l) - rhs_l
                    let mut sum_rest = 0i128;
                    for (&u, &c) in rest_l {
                        let Some(prod) = c.checked_mul(model[u]) else {
                            return LiaResult::Unknown;
                        };
                        let Some(next) = sum_rest.checked_add(prod) else {
                            return LiaResult::Unknown;
                        };
                        sum_rest = next;
                    }
                    let Some(num) = sum_rest.checked_sub(*rhs_l) else {
                        return LiaResult::Unknown;
                    };
                    let cand_lb = ceil_div_i128(num, *a_l);
                    if cand_lb > lb {
                        lb = cand_lb;
                    }
                }
                for (a_u, rest_u, rhs_u) in &upper {
                    // a_u * var + sum(rest_u) <= rhs_u  <=>  a_u * var <= rhs_u - sum(rest_u)
                    let mut sum_rest = 0i128;
                    for (&u, &c) in rest_u {
                        let Some(prod) = c.checked_mul(model[u]) else {
                            return LiaResult::Unknown;
                        };
                        let Some(next) = sum_rest.checked_add(prod) else {
                            return LiaResult::Unknown;
                        };
                        sum_rest = next;
                    }
                    let Some(num) = rhs_u.checked_sub(sum_rest) else {
                        return LiaResult::Unknown;
                    };
                    let cand_ub = num.div_euclid(*a_u);
                    if cand_ub < ub {
                        ub = cand_ub;
                    }
                }
                if lb <= ub {
                    model[var] = if lb <= 0 && 0 <= ub {
                        0
                    } else if lb > 0 {
                        lb
                    } else {
                        ub
                    };
                } else {
                    // Dark-shadow splinter: try exact Omega splinters on the tightest side
                    return solve_omega_splinters(
                        constraints,
                        num_vars,
                        var,
                        &lower,
                        &upper,
                        steps,
                        depth + 1,
                    );
                }
            }
        }
    }

    LiaResult::Sat(model)
}

fn solve_omega_splinters(
    constraints: &[LeqConstraint],
    num_vars: usize,
    var: usize,
    lower: &[(i128, BTreeMap<usize, i128>, i128)],
    upper: &[(i128, BTreeMap<usize, i128>, i128)],
    steps: &mut usize,
    depth: usize,
) -> LiaResult {
    // Omega Test exact splinter rule (Pugh 1991):
    // When real shadow holds (`a_u * L <= a_l * U`) but no integer `var` satisfies both,
    // any integer solution must satisfy `a_l * var == L + rem` (or `a_u * var == U - rem`)
    // for some remainder `0 <= rem < a_l` (or `0 <= rem < a_u`).
    let max_a_l = lower.iter().map(|(a, _, _)| *a).max().unwrap_or(1);
    let max_a_u = upper.iter().map(|(a, _, _)| *a).max().unwrap_or(1);
    if max_a_l.min(max_a_u) > 32 {
        return LiaResult::Unknown;
    }

    let make_eq_splinter = |coeffs: BTreeMap<usize, i128>, rhs: i128| -> Option<[LeqConstraint; 2]> {
        let neg_rhs = rhs.checked_neg()?;
        let c1 = match normalize_leq_zero(&LinExpr {
            coeffs: coeffs.clone(),
            constant: neg_rhs,
        })? {
            NormLeq::Constraint(c) => c,
            _ => return None,
        };
        let mut neg_coeffs = BTreeMap::new();
        for (&u, &c) in &coeffs {
            neg_coeffs.insert(u, c.checked_neg()?);
        }
        let c2 = match normalize_leq_zero(&LinExpr {
            coeffs: neg_coeffs,
            constant: rhs,
        })? {
            NormLeq::Constraint(c) => c,
            _ => return None,
        };
        Some([c1, c2])
    };

    if max_a_l <= max_a_u {
        for (a_l, rest_l, rhs_l) in lower {
            if *a_l <= 1 {
                continue;
            }
            for rem in 0..*a_l {
                let Some(target_rhs) = rhs_l.checked_sub(rem) else {
                    return LiaResult::Unknown;
                };
                let mut c1_coeffs = rest_l.clone();
                c1_coeffs.insert(var, -*a_l);
                let Some([c1, c2]) = make_eq_splinter(c1_coeffs, target_rhs) else {
                    continue;
                };
                let mut next = constraints.to_vec();
                next.push(c1);
                next.push(c2);
                match solve_qf_lia_inner(&next, num_vars, steps, depth) {
                    LiaResult::Sat(m) => return LiaResult::Sat(m),
                    LiaResult::Unknown => return LiaResult::Unknown,
                    LiaResult::Unsat => {}
                }
            }
        }
    } else {
        for (a_u, rest_u, rhs_u) in upper {
            if *a_u <= 1 {
                continue;
            }
            for rem in 0..*a_u {
                let Some(target_rhs) = rhs_u.checked_sub(rem) else {
                    return LiaResult::Unknown;
                };
                let mut c1_coeffs = rest_u.clone();
                c1_coeffs.insert(var, *a_u);
                let Some([c1, c2]) = make_eq_splinter(c1_coeffs, target_rhs) else {
                    continue;
                };
                let mut next = constraints.to_vec();
                next.push(c1);
                next.push(c2);
                match solve_qf_lia_inner(&next, num_vars, steps, depth) {
                    LiaResult::Sat(m) => return LiaResult::Sat(m),
                    LiaResult::Unknown => return LiaResult::Unknown,
                    LiaResult::Unsat => {}
                }
            }
        }
    }
    LiaResult::Unsat
}

fn substitute_linear_eq(
    active: &BTreeSet<LeqConstraint>,
    var: usize,
    denom: i128,
    rest: &BTreeMap<usize, i128>,
    rhs: i128,
) -> Option<Result<BTreeSet<LeqConstraint>, ()>> {
    // We have `denom * var == rhs - sum(rest)`.
    // Normalize so `abs_d = |denom| > 0` and `abs_d * var == s_rhs - sum(s_rest)`.
    let (abs_d, s_rest, s_rhs) = if denom > 0 {
        (denom, rest.clone(), rhs)
    } else {
        let mut nr = BTreeMap::new();
        for (&u, &c) in rest {
            nr.insert(u, c.checked_neg()?);
        }
        (denom.checked_neg()?, nr, rhs.checked_neg()?)
    };

    let mut next = BTreeSet::new();
    for c in active {
        if let Some(&a) = c.coeffs.get(&var) {
            // Multiply constraint `a * var + sum_{u != var} c_u * u <= c.rhs` by `abs_d > 0`:
            // `a * (s_rhs - sum(s_rest)) + abs_d * sum_{u != var} c_u * u <= abs_d * c.rhs`
            // `<=> sum_u (abs_d * c_u - a * s_rest_u) * u <= abs_d * c.rhs - a * s_rhs`
            let mut new_coeffs = BTreeMap::new();
            for (&u, &cu) in &c.coeffs {
                if u == var {
                    continue;
                }
                let term = abs_d.checked_mul(cu)?;
                if term != 0 {
                    new_coeffs.insert(u, term);
                }
            }
            for (&u, &ru) in &s_rest {
                let sub_term = a.checked_mul(ru)?;
                let prev = new_coeffs.get(&u).copied().unwrap_or(0);
                let diff = prev.checked_sub(sub_term)?;
                if diff == 0 {
                    new_coeffs.remove(&u);
                } else {
                    new_coeffs.insert(u, diff);
                }
            }
            let new_rhs = abs_d
                .checked_mul(c.rhs)?
                .checked_sub(a.checked_mul(s_rhs)?)?;
            let neg_rhs = new_rhs.checked_neg()?;
            let lin = LinExpr {
                coeffs: new_coeffs,
                constant: neg_rhs,
            };
            match normalize_leq_zero(&lin)? {
                NormLeq::AlwaysTrue => {}
                NormLeq::AlwaysFalse => return Some(Err(())),
                NormLeq::Constraint(nc) => {
                    next.insert(nc);
                }
            }
        } else {
            next.insert(c.clone());
        }
    }
    Some(Ok(next))
}

fn substitute_var(
    active: &BTreeSet<LeqConstraint>,
    var: usize,
    val: i128,
) -> Option<Result<BTreeSet<LeqConstraint>, ()>> {
    let mut next = BTreeSet::new();
    for c in active {
        if let Some(&a) = c.coeffs.get(&var) {
            let mut coeffs = c.coeffs.clone();
            coeffs.remove(&var);
            let prod = a.checked_mul(val)?;
            let new_rhs = c.rhs.checked_sub(prod)?;
            let neg_rhs = new_rhs.checked_neg()?;
            let lin = LinExpr {
                coeffs,
                constant: neg_rhs,
            };
            match normalize_leq_zero(&lin)? {
                NormLeq::AlwaysTrue => {}
                NormLeq::AlwaysFalse => return Some(Err(())),
                NormLeq::Constraint(nc) => {
                    next.insert(nc);
                }
            }
        } else {
            next.insert(c.clone());
        }
    }
    Some(Ok(next))
}

#[derive(Debug, Clone)]
enum SolveOutcome {
    Sat {
        bool_model: BTreeMap<usize, bool>,
        int_model: Vec<i128>,
    },
    Unsat,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TruthVal {
    True,
    False,
    Undef,
}

fn eval_partial(
    f: &Formula,
    bool_model: &BTreeMap<usize, bool>,
    active_leqs: &BTreeSet<LeqConstraint>,
) -> TruthVal {
    match f {
        Formula::True => TruthVal::True,
        Formula::False => TruthVal::False,
        Formula::BoolVar(v, pol) => match bool_model.get(v) {
            Some(&val) => {
                if val == *pol {
                    TruthVal::True
                } else {
                    TruthVal::False
                }
            }
            None => TruthVal::Undef,
        },
        Formula::Leq(c) => {
            if active_leqs.contains(c) {
                return TruthVal::True;
            }
            // Check if negation `sum (-a_i) x_i <= -rhs - 1` or any stronger bound on same lhs is active
            for act in active_leqs {
                if act.coeffs == c.coeffs && act.rhs <= c.rhs {
                    return TruthVal::True;
                }
                if act.coeffs.len() == c.coeffs.len()
                    && act.coeffs.iter().all(|(k, v)| c.coeffs.get(k) == Some(&-*v))
                    && act.rhs < -c.rhs
                {
                    return TruthVal::False;
                }
            }
            TruthVal::Undef
        }
        Formula::Not(inner) => match eval_partial(inner, bool_model, active_leqs) {
            TruthVal::True => TruthVal::False,
            TruthVal::False => TruthVal::True,
            TruthVal::Undef => TruthVal::Undef,
        },
        Formula::And(items) => {
            let mut all_true = true;
            for it in items {
                match eval_partial(it, bool_model, active_leqs) {
                    TruthVal::False => return TruthVal::False,
                    TruthVal::Undef => all_true = false,
                    TruthVal::True => {}
                }
            }
            if all_true {
                TruthVal::True
            } else {
                TruthVal::Undef
            }
        }
        Formula::Or(items) => {
            let mut all_false = true;
            for it in items {
                match eval_partial(it, bool_model, active_leqs) {
                    TruthVal::True => return TruthVal::True,
                    TruthVal::Undef => all_false = false,
                    TruthVal::False => {}
                }
            }
            if all_false {
                TruthVal::False
            } else {
                TruthVal::Undef
            }
        }
    }
}

fn dpll_solve(
    goals: Vec<Formula>,
    bool_model: &mut BTreeMap<usize, bool>,
    lia_constraints: &mut Vec<LeqConstraint>,
    num_int_vars: usize,
    steps: &mut usize,
) -> SolveOutcome {
    *steps += 1;
    if *steps > MAX_SOLVER_STEPS {
        return SolveOutcome::Unknown;
    }

    let mut pending = goals;
    let mut disjunctions: Vec<Vec<Formula>> = Vec::new();
    let base_lia_len = lia_constraints.len();
    let mut assigned_bools: Vec<usize> = Vec::new();
    let mut active_leqs: BTreeSet<LeqConstraint> = lia_constraints.iter().cloned().collect();

    // Fixed-point unit + theory-atom propagation
    let mut conflict = false;
    loop {
        while let Some(f) = pending.pop() {
            match f {
                Formula::True => {}
                Formula::False => {
                    conflict = true;
                    break;
                }
                Formula::BoolVar(v, pol) => {
                    if let Some(&existing) = bool_model.get(&v) {
                        if existing != pol {
                            conflict = true;
                            break;
                        }
                    } else {
                        bool_model.insert(v, pol);
                        assigned_bools.push(v);
                    }
                }
                Formula::Leq(c) => {
                    if eval_partial(&Formula::Leq(c.clone()), bool_model, &active_leqs)
                        == TruthVal::False
                    {
                        conflict = true;
                        break;
                    }
                    if active_leqs.insert(c.clone()) {
                        lia_constraints.push(c);
                    }
                }
                Formula::Not(inner) => {
                    pending.push(negate_nnf(*inner));
                }
                Formula::And(items) => {
                    for it in items.into_iter().rev() {
                        pending.push(it);
                    }
                }
                Formula::Or(items) => {
                    disjunctions.push(items);
                }
            }
        }
        if conflict {
            break;
        }

        // Simplify all disjunctions against currently known bools and active linear inequalities
        let mut unit_propagated = false;
        let mut next_disjunctions = Vec::with_capacity(disjunctions.len());
        for disj in disjunctions {
            let mut simplified = Vec::new();
            let mut satisfied = false;
            for lit in disj {
                match eval_partial(&lit, bool_model, &active_leqs) {
                    TruthVal::True => {
                        satisfied = true;
                        break;
                    }
                    TruthVal::False => {}
                    TruthVal::Undef => {
                        if !simplified.contains(&lit) {
                            simplified.push(lit);
                        }
                    }
                }
            }
            if !satisfied {
                match simplified.len() {
                    0 => {
                        conflict = true;
                        break;
                    }
                    1 => {
                        pending.push(simplified.into_iter().next().unwrap());
                        unit_propagated = true;
                    }
                    _ => next_disjunctions.push(simplified),
                }
            }
        }
        disjunctions = next_disjunctions;
        if conflict || !unit_propagated {
            break;
        }
    }

    if conflict {
        lia_constraints.truncate(base_lia_len);
        for v in assigned_bools {
            bool_model.remove(&v);
        }
        return SolveOutcome::Unsat;
    }

    // Eager DPLL(T) theory check: if new LIA constraints were added at this level (or at a leaf),
    // check LIA feasibility now so infeasible branches are pruned immediately.
    if disjunctions.is_empty() || lia_constraints.len() > base_lia_len {
        match solve_qf_lia(lia_constraints, num_int_vars, steps) {
            LiaResult::Unsat => {
                lia_constraints.truncate(base_lia_len);
                for v in assigned_bools {
                    bool_model.remove(&v);
                }
                return SolveOutcome::Unsat;
            }
            LiaResult::Unknown => {
                lia_constraints.truncate(base_lia_len);
                for v in assigned_bools {
                    bool_model.remove(&v);
                }
                return SolveOutcome::Unknown;
            }
            LiaResult::Sat(int_model) => {
                if disjunctions.is_empty() {
                    let sat_bool_model = bool_model.clone();
                    lia_constraints.truncate(base_lia_len);
                    for v in assigned_bools {
                        bool_model.remove(&v);
                    }
                    return SolveOutcome::Sat {
                        bool_model: sat_bool_model,
                        int_model,
                    };
                }
            }
        }
    }

    // Pick shortest disjunction (MRV heuristic)
    let mut best_idx = 0;
    for i in 1..disjunctions.len() {
        if disjunctions[i].len() < disjunctions[best_idx].len() {
            best_idx = i;
        }
    }
    let choices = disjunctions.swap_remove(best_idx);

    let mut saw_unknown = false;
    for branch in choices {
        let mut next_goals: Vec<Formula> = disjunctions
            .iter()
            .cloned()
            .map(Formula::Or)
            .collect();
        next_goals.push(branch);
        match dpll_solve(next_goals, bool_model, lia_constraints, num_int_vars, steps) {
            SolveOutcome::Sat {
                bool_model: bm,
                int_model: im,
            } => {
                lia_constraints.truncate(base_lia_len);
                for v in assigned_bools {
                    bool_model.remove(&v);
                }
                return SolveOutcome::Sat {
                    bool_model: bm,
                    int_model: im,
                };
            }
            SolveOutcome::Unknown => {
                saw_unknown = true;
            }
            SolveOutcome::Unsat => {}
        }
    }

    lia_constraints.truncate(base_lia_len);
    for v in assigned_bools {
        bool_model.remove(&v);
    }
    if saw_unknown {
        SolveOutcome::Unknown
    } else {
        SolveOutcome::Unsat
    }
}

fn negate_nnf(f: Formula) -> Formula {
    match f {
        Formula::True => Formula::False,
        Formula::False => Formula::True,
        Formula::BoolVar(v, pol) => Formula::BoolVar(v, !pol),
        Formula::Not(inner) => *inner,
        Formula::Leq(c) => Formula::not(Formula::Leq(c)),
        Formula::And(items) => Formula::Or(items.into_iter().map(negate_nnf).collect()),
        Formula::Or(items) => Formula::And(items.into_iter().map(negate_nnf).collect()),
    }
}

fn eval_formula_under_model(
    f: &Formula,
    bool_model: &BTreeMap<usize, bool>,
    int_model: &[i128],
) -> Option<bool> {
    match f {
        Formula::True => Some(true),
        Formula::False => Some(false),
        Formula::BoolVar(v, pol) => {
            let val = bool_model.get(v).copied().unwrap_or(false);
            Some(val == *pol)
        }
        Formula::Leq(c) => {
            let mut sum = 0i128;
            for (&v, &a) in &c.coeffs {
                let val = *int_model.get(v)?;
                sum = sum.checked_add(a.checked_mul(val)?)?;
            }
            Some(sum <= c.rhs)
        }
        Formula::Not(inner) => Some(!eval_formula_under_model(inner, bool_model, int_model)?),
        Formula::And(items) => {
            for it in items {
                if !eval_formula_under_model(it, bool_model, int_model)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        Formula::Or(items) => {
            for it in items {
                if eval_formula_under_model(it, bool_model, int_model)? {
                    return Some(true);
                }
            }
            Some(false)
        }
    }
}

#[derive(Debug, Clone)]
enum CheckSatOutcome {
    Sat(String),
    Unsat,
    Unknown,
}

fn solve_scope(scope: &Scope) -> CheckSatOutcome {
    let entity_eq = scope
        .assertions
        .iter()
        .any(|a| expr_uses_entity_equality_or_ite(a, scope, &BTreeMap::new()));
    let mut ctx = LoweringCtx::new(scope, entity_eq);

    // Pre-allocate all declared Int and Bool constants so `(get-model)` includes every declared
    // constant deterministically.
    for (name, &sort) in &scope.consts {
        if scope.defined_ints.contains_key(name) || name == "__entity_witness" {
            continue;
        }
        match sort {
            SmtSort::Int => {
                ctx.get_or_alloc_int_var(name);
            }
            SmtSort::Bool => {
                ctx.get_or_alloc_bool_var(name);
            }
            _ => {}
        }
    }

    let mut formulas = Vec::with_capacity(scope.assertions.len());
    for assertion in &scope.assertions {
        let Some(LoweredTerm::Bool(f)) = ctx.lower_term(assertion, &BTreeMap::new()) else {
            return CheckSatOutcome::Unknown;
        };
        formulas.push(f);
    }
    formulas.extend(ctx.side_constraints.clone());

    let mut bool_model = BTreeMap::new();
    let mut lia_constraints = Vec::new();
    let mut steps = 0usize;
    let num_int_vars = ctx.int_var_names.len();

    match dpll_solve(
        formulas.clone(),
        &mut bool_model,
        &mut lia_constraints,
        num_int_vars,
        &mut steps,
    ) {
        SolveOutcome::Unsat => CheckSatOutcome::Unsat,
        SolveOutcome::Unknown => CheckSatOutcome::Unknown,
        SolveOutcome::Sat {
            bool_model,
            int_model,
        } => {
            // Soundness guard: independently verify that the candidate model satisfies every
            // lowered assertion and side constraint before reporting `sat`.
            for f in &formulas {
                if eval_formula_under_model(f, &bool_model, &int_model) != Some(true) {
                    return CheckSatOutcome::Unknown;
                }
            }
            let mut model_lines = Vec::new();
            model_lines.push("(".to_string());
            for (name, &sort) in &scope.consts {
                if scope.defined_ints.contains_key(name) || name == "__entity_witness" {
                    continue;
                }
                match sort {
                    SmtSort::Int => {
                        let v = ctx.int_var_ids.get(name).copied().unwrap_or(0);
                        let val = int_model.get(v).copied().unwrap_or(0);
                        let val_str = if val < 0 {
                            format!("(- {})", -val)
                        } else {
                            val.to_string()
                        };
                        model_lines.push(format!("  (define-fun {} () Int {})", name, val_str));
                    }
                    SmtSort::Bool => {
                        let v = ctx.bool_var_ids.get(name).copied().unwrap_or(0);
                        let val = bool_model.get(&v).copied().unwrap_or(false);
                        model_lines.push(format!("  (define-fun {} () Bool {})", name, val));
                    }
                    _ => {}
                }
            }
            model_lines.push(")".to_string());
            CheckSatOutcome::Sat(model_lines.join("\n") + "\n")
        }
    }
}

/// Entry point for the in-repo `bil-smt` backend behind `--prover bil-smt`.
///
/// Validates that `smt2_input` belongs to the decidable `bil-smt` fragment, instantiates universal
/// `Entity` quantifiers over the finite Herbrand universe, and executes the incremental command
/// stream (`assert`, `push`, `pop`, `check-sat`, `get-model`) using the exact `QF_UFLIA` decision
/// procedure. Outside the fragment (or on arithmetic overflow / step limit), returns
/// `Verdict::Unknown` (never a guess).
pub fn run_bil_smt(smt2_input: &str) -> ProverResult {
    let start = Instant::now();
    let qf_script = match instantiate_entity_quantifiers(smt2_input) {
        Ok(s) => s,
        Err(reason) => {
            return ProverResult {
                prover: "bil-smt".to_string(),
                verdict: Verdict::Unknown,
                stdout: "unknown\n".to_string(),
                stderr: String::new(),
                elapsed_ms: start.elapsed().as_millis(),
                detail: format!("outside bil-smt fragment: {}", reason),
            };
        }
    };

    let Some(forms) = parse_sexprs(&qf_script) else {
        return ProverResult {
            prover: "bil-smt".to_string(),
            verdict: Verdict::Unknown,
            stdout: "unknown\n".to_string(),
            stderr: String::new(),
            elapsed_ms: start.elapsed().as_millis(),
            detail: "outside bil-smt fragment: malformed instantiated script".to_string(),
        };
    };

    let mut scope = Scope::default();
    let mut stack: Vec<Scope> = Vec::new();
    let mut stdout = String::new();
    let mut first_verdict: Option<(Verdict, String)> = None;
    let mut last_model: Option<String> = None;

    for form in &forms {
        let SExpr::List(items) = form else {
            continue;
        };
        let Some(SExpr::Atom(cmd)) = items.first() else {
            continue;
        };
        match cmd.as_str() {
            "declare-const" => {
                if let (SExpr::Atom(name), SExpr::Atom(sort_name)) = (&items[1], &items[2]) {
                    let sort = SmtSort::parse(sort_name).unwrap();
                    if sort == SmtSort::Entity && !scope.entity_consts.contains(name) {
                        scope.entity_consts.push(name.clone());
                    }
                    scope.consts.insert(name.clone(), sort);
                }
            }
            "define-const" => {
                if let (SExpr::Atom(name), _, val_expr) = (&items[1], &items[2], &items[3]) {
                    let k = eval_const_int(val_expr, &scope.defined_ints).unwrap();
                    scope.consts.insert(name.clone(), SmtSort::Int);
                    scope.defined_ints.insert(name.clone(), k);
                }
            }
            "declare-fun" => {
                if let (SExpr::Atom(name), SExpr::List(arg_sorts), SExpr::Atom(ret_name)) =
                    (&items[1], &items[2], &items[3])
                {
                    let ret = SmtSort::parse(ret_name).unwrap();
                    if arg_sorts.is_empty() {
                        if ret == SmtSort::Entity && !scope.entity_consts.contains(name) {
                            scope.entity_consts.push(name.clone());
                        }
                        scope.consts.insert(name.clone(), ret);
                    } else {
                        scope.funs.insert(
                            name.clone(),
                            FunSig {
                                args: vec![SmtSort::Entity; arg_sorts.len()],
                                ret,
                            },
                        );
                    }
                }
            }
            "push" => {
                let n = items
                    .get(1)
                    .and_then(|x| match x {
                        SExpr::Atom(a) => a.parse::<usize>().ok(),
                        _ => None,
                    })
                    .unwrap_or(1);
                for _ in 0..n {
                    stack.push(scope.clone());
                }
            }
            "pop" => {
                let n = items
                    .get(1)
                    .and_then(|x| match x {
                        SExpr::Atom(a) => a.parse::<usize>().ok(),
                        _ => None,
                    })
                    .unwrap_or(1);
                for _ in 0..n {
                    if let Some(prev) = stack.pop() {
                        scope = prev;
                    }
                }
            }
            "assert" => {
                if items.len() == 2 {
                    scope.assertions.push(items[1].clone());
                }
            }
            "check-sat" => match solve_scope(&scope) {
                CheckSatOutcome::Sat(model_str) => {
                    stdout.push_str("sat\n");
                    last_model = Some(model_str);
                    if first_verdict.is_none() {
                        first_verdict = Some((
                            Verdict::Consistent,
                            "bil-smt found satisfying model (sat)".to_string(),
                        ));
                    }
                }
                CheckSatOutcome::Unsat => {
                    stdout.push_str("unsat\n");
                    last_model = None;
                    if first_verdict.is_none() {
                        first_verdict = Some((
                            Verdict::Inconsistent,
                            "bil-smt proved unsatisfiable (unsat)".to_string(),
                        ));
                    }
                }
                CheckSatOutcome::Unknown => {
                    stdout.push_str("unknown\n");
                    last_model = None;
                    if first_verdict.is_none() {
                        first_verdict = Some((
                            Verdict::Unknown,
                            "bil-smt inconclusive (unknown)".to_string(),
                        ));
                    }
                }
            },
            "get-model" => {
                if let Some(ref m) = last_model {
                    stdout.push_str(m);
                }
            }
            _ => {}
        }
    }

    let (verdict, detail) = first_verdict
        .unwrap_or_else(|| (Verdict::Unknown, "bil-smt no check-sat command".to_string()));
    if stdout.is_empty() {
        stdout.push_str("unknown\n");
    }

    ProverResult {
        prover: "bil-smt".to_string(),
        verdict,
        stdout,
        stderr: String::new(),
        elapsed_ms: start.elapsed().as_millis(),
        detail,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model_check::{emit_symbolic_bmc_smt2, symbolic_bmc_program};
    use crate::smt::{
        attach_model, emit_ontology_consistency_smt2, emit_subsumption_smt2, find_solver_binary,
        parse_smt_model, prove_subsumption, run_smt_incremental_batch_with_prover, run_smt_prover,
        Prover, SolverBackend, SubsumptionResult,
    };
    use crate::wp::generate_obligations;
    use crate::CompilationSession;
    use std::path::PathBuf;

    fn domain_files() -> Vec<PathBuf> {
        let mut files: Vec<PathBuf> = std::fs::read_dir("examples/domains")
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|x| x == "bil"))
            .collect();
        files.sort();
        files
    }

    #[test]
    fn every_domain_example_vc_ontology_subsumption_and_bmc_matches_z3() {
        let has_z3 = find_solver_binary("z3").is_some();
        let files = domain_files();
        assert_eq!(files.len(), 14);
        let mut total_obligations = 0usize;
        let mut quantified_obligations = 0usize;
        let mut z3_batch = String::new();
        let mut expected_verdicts: Vec<(String, &'static str)> = Vec::new();
        let mut bmc_systems_checked = 0usize;

        for path in files {
            let src = std::fs::read_to_string(&path).unwrap();
            let session = CompilationSession::from_source(&src).unwrap();

            // 1. Check ontology consistency script if axioms exist
            let has_axioms = session
                .program
                .items
                .iter()
                .any(|i| matches!(i, crate::ast::Item::Axiom(_)));
            if has_axioms {
                let ont_smt2 =
                    emit_ontology_consistency_smt2(&session.program, &session.ontology);
                let qf = instantiate_entity_quantifiers(&ont_smt2).unwrap_or_else(|e| {
                    panic!(
                        "{}: ontology consistency script rejected by fragment checker: {}",
                        path.display(),
                        e
                    )
                });
                assert!(!qf.contains("(forall"));
                let bil_res = run_bil_smt(&ont_smt2);
                assert_eq!(
                    bil_res.verdict,
                    Verdict::Consistent,
                    "{}: expected ontology consistency SAT from bil-smt, got {:?}",
                    path.display(),
                    bil_res
                );
                if has_z3 {
                    z3_batch.push_str("(reset)\n");
                    z3_batch.push_str(&ont_smt2);
                    z3_batch.push_str("(reset)\n");
                    z3_batch.push_str(&qf);
                    expected_verdicts.push((format!("{}::ontology", path.display()), "sat"));
                }
            }

            // 2. Check prove_subsumption on declared concept hierarchy edges
            for (cname, cinfo) in &session.ontology.concepts {
                if let Some(parent) = &cinfo.parent {
                    let sub_res = prove_subsumption(
                        &session.program,
                        &session.ontology,
                        cname,
                        parent,
                        Prover::BilSmt,
                    );
                    assert_eq!(
                        sub_res,
                        SubsumptionResult::Subsumed {
                            prover: "bil-smt".to_string()
                        },
                        "{}: expected {} <: {} subsumed by bil-smt",
                        path.display(),
                        cname,
                        parent
                    );
                    let rev_res = prove_subsumption(
                        &session.program,
                        &session.ontology,
                        parent,
                        cname,
                        Prover::BilSmt,
                    );
                    assert!(
                        matches!(rev_res, SubsumptionResult::NotSubsumed { .. }),
                        "{}: expected parent {} not subsumed by child {}",
                        path.display(),
                        parent,
                        cname
                    );
                }
            }

            // 3. Check every VC obligation script
            let obs = generate_obligations(&session.program, &session.ontology);
            for ob in obs {
                let script = ob.smt2_script.unwrap_or_else(|| {
                    panic!(
                        "{}::{}: expected SMT-LIB2 script",
                        path.display(),
                        ob.fn_name
                    )
                });
                total_obligations += 1;
                if script.contains("(forall") {
                    quantified_obligations += 1;
                }
                let qf = instantiate_entity_quantifiers(&script).unwrap_or_else(|e| {
                    panic!(
                        "{}::{} ({}): rejected by fragment checker: {}\n{}",
                        path.display(),
                        ob.fn_name,
                        ob.kind,
                        e,
                        script
                    )
                });
                assert!(!qf.contains("(forall"));
                let bil_res = run_bil_smt(&script);
                assert_eq!(
                    bil_res.verdict,
                    Verdict::Inconsistent,
                    "{}::{} ({}): expected unsat from bil-smt, got {:?}\n{}",
                    path.display(),
                    ob.fn_name,
                    ob.kind,
                    bil_res,
                    script
                );
                if has_z3 {
                    z3_batch.push_str("(reset)\n");
                    z3_batch.push_str(&script);
                    z3_batch.push_str("(reset)\n");
                    z3_batch.push_str(&qf);
                    expected_verdicts.push((
                        format!("{}::{} ({})", path.display(), ob.fn_name, ob.kind),
                        "unsat",
                    ));
                }
            }

            // 4. Check symbolic BMC (k = 3) with Prover::BilSmt
            let bmc_reports =
                symbolic_bmc_program(&session.program, &session.ontology, 3, Prover::BilSmt);
            for rep in bmc_reports {
                bmc_systems_checked += 1;
                assert!(
                    rep.safe_up_to_k,
                    "{}::{}: expected BMC k=3 safe under bil-smt, got {:?}",
                    path.display(),
                    rep.system_name,
                    rep.verdict
                );
                assert_eq!(rep.verdict, Verdict::Inconsistent);
            }
        }
        if has_z3 {
            let res = run_smt_prover(Prover::Z3, &z3_batch);
            let verdicts: Vec<&str> = res
                .stdout
                .lines()
                .map(str::trim)
                .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
                .collect();
            assert_eq!(
                verdicts.len(),
                expected_verdicts.len() * 2,
                "expected {} z3 verdicts, got {}",
                expected_verdicts.len() * 2,
                verdicts.len()
            );
            for (pair, (label, expected)) in verdicts.chunks(2).zip(&expected_verdicts) {
                assert_eq!(
                    pair[0], pair[1],
                    "{}: z3 verdict differed after Entity instantiation ({} vs {})",
                    label, pair[0], pair[1]
                );
                assert_eq!(&pair[0], expected, "{}: unexpected z3 verdict", label);
            }
        }
        assert_eq!(total_obligations, 147);
        assert!(quantified_obligations > 0);
        assert_eq!(bmc_systems_checked, 4);
    }

    #[test]
    fn seeded_bug_refutation_and_counterexample_model_extraction_work_in_bil_smt() {
        let src =
            std::fs::read_to_string("examples/domains/seeded_bugs/reactor_trip_shared_input.bil")
                .unwrap();
        let session = CompilationSession::from_source(&src).unwrap();
        let obs = generate_obligations(&session.program, &session.ontology);
        let trip_ob = obs
            .iter()
            .find(|o| o.fn_name == "high_temp_trip")
            .unwrap();
        let script = trip_ob.smt2_script.as_ref().unwrap();
        let bil_res = run_bil_smt(script);
        assert_eq!(bil_res.verdict, Verdict::Consistent);

        let with_model = attach_model(bil_res, script);
        let parsed = parse_smt_model(&with_model.stdout).expect("expected parsed counterexample");
        assert!(
            parsed.contains("setpoint =")
                && parsed.contains("t1 =")
                && parsed.contains("t2 =")
                && parsed.contains("t3 ="),
            "unexpected model format: {}",
            parsed
        );

        if find_solver_binary("z3").is_some() {
            let orig_res = run_smt_prover(Prover::Z3, script);
            assert_eq!(orig_res.verdict, Verdict::Consistent);
        }
    }

    #[test]
    fn incremental_batch_div_mod_lia_strings_and_ackermann_match_z3() {
        // 1. Incremental batch push/pop
        let base = "(set-logic ALL)\n(declare-const x Int)\n(assert (> x 10))\n";
        let refs = vec![
            "(<= x 5)".to_string(),
            "(> x 20)".to_string(),
            "(= x 10)".to_string(),
        ];
        let (prover_name, verdicts) =
            run_smt_incremental_batch_with_prover(Prover::BilSmt, base, &refs).unwrap();
        assert_eq!(prover_name, "bil-smt");
        assert_eq!(
            verdicts,
            vec![
                Verdict::Inconsistent,
                Verdict::Consistent,
                Verdict::Inconsistent
            ]
        );

        // 2. Non-unit LIA, GCD infeasibility, Omega splinter, div/mod, abs, ite, let, String, Entity eq
        let queries = [
            // GCD parity infeasibility: 2x - 2y = 1 (unsat)
            (
                "(set-logic ALL)\n(declare-const x Int)\n(declare-const y Int)\n(assert (= (- (* 2 x) (* 2 y)) 1))\n(check-sat)\n",
                Verdict::Inconsistent,
            ),
            // Omega dark shadow splinter: 27 <= 11x + 13y <= 45 and -10 <= 7x - 9y <= 4 (unsat in Int, sat in Real)
            (
                "(set-logic ALL)\n(declare-const x Int)\n(declare-const y Int)\n(assert (<= 27 (+ (* 11 x) (* 13 y))))\n(assert (<= (+ (* 11 x) (* 13 y)) 45))\n(assert (<= (- 10) (- (* 7 x) (* 9 y))))\n(assert (<= (- (* 7 x) (* 9 y)) 4))\n(check-sat)\n",
                Verdict::Inconsistent,
            ),
            // Non-unit satisfiable system: 3x + 2y = 7 and x >= 1 and y >= 1 (sat: x=1, y=2)
            (
                "(set-logic ALL)\n(declare-const x Int)\n(declare-const y Int)\n(assert (= (+ (* 3 x) (* 2 y)) 7))\n(assert (>= x 1))\n(assert (>= y 1))\n(check-sat)\n(get-model)\n",
                Verdict::Consistent,
            ),
            // Euclidean div and mod identity: x = 5 * (div x 5) + (mod x 5) is valid -> negation unsat
            (
                "(set-logic ALL)\n(declare-const x Int)\n(assert (not (= x (+ (* 5 (div x 5)) (mod x 5)))))\n(check-sat)\n",
                Verdict::Inconsistent,
            ),
            // abs and ite and let
            (
                "(set-logic ALL)\n(declare-const x Int)\n(assert (let ((a (abs x)) (b (ite (>= x 0) x (- x)))) (distinct a b)))\n(check-sat)\n",
                Verdict::Inconsistent,
            ),
            // String equality and disequality
            (
                "(set-logic ALL)\n(declare-const s String)\n(assert (= s \"alpha\"))\n(assert (= s \"beta\"))\n(check-sat)\n",
                Verdict::Inconsistent,
            ),
            (
                "(set-logic ALL)\n(declare-const s String)\n(assert (distinct s \"alpha\"))\n(assert (distinct s \"beta\"))\n(check-sat)\n",
                Verdict::Consistent,
            ),
            // Uninterpreted function congruence over Entity equality: a = b && f(a) != f(b) is unsat
            (
                "(set-logic ALL)\n(declare-sort Entity 0)\n(declare-const a Entity)\n(declare-const b Entity)\n(declare-fun f (Entity) Int)\n(assert (= a b))\n(assert (distinct (f a) (f b)))\n(check-sat)\n",
                Verdict::Inconsistent,
            ),
            // Quantifier over Entity with no declared Entity constants (uses __entity_witness)
            (
                "(set-logic ALL)\n(declare-sort Entity 0)\n(declare-fun p (Entity) Bool)\n(assert (forall ((x Entity)) (and (p x) (not (p x)))))\n(check-sat)\n",
                Verdict::Inconsistent,
            ),
        ];

        let has_z3 = find_solver_binary("z3").is_some();
        for (script, expected) in queries {
            let bil_res = run_bil_smt(script);
            assert_eq!(
                bil_res.verdict, expected,
                "unexpected bil-smt verdict for:\n{}",
                script
            );
            if has_z3 {
                let z3_res = run_smt_prover(Prover::Z3, script);
                assert_eq!(
                    bil_res.verdict, z3_res.verdict,
                    "bil-smt disagreed with z3 on:\n{}",
                    script
                );
            }
        }
    }

    #[test]
    fn out_of_fragment_scripts_are_rejected_and_return_unknown() {
        let cases = [
            // Malformed S-expression
            "(set-logic ALL\n(check-sat)",
            // Unsupported sort Real
            "(set-logic ALL)\n(declare-const x Real)\n(assert (> x 0.0))\n(check-sat)",
            // Existential quantifier
            "(set-logic ALL)\n(declare-sort Entity 0)\n(declare-fun p (Entity) Bool)\n(assert (exists ((x Entity)) (p x)))\n(check-sat)",
            // Universal quantifier over Int (e.g. recursive function unfolding or range quantifier)
            "(set-logic ALL)\n(assert (forall ((n Int)) (>= (* n n) 0)))\n(check-sat)",
            // Nonlinear multiplication
            "(set-logic ALL)\n(declare-const x Int)\n(declare-const y Int)\n(assert (= (* x y) 12))\n(check-sat)",
            // Division by variable
            "(set-logic ALL)\n(declare-const x Int)\n(declare-const y Int)\n(assert (= (div x y) 1))\n(check-sat)",
            // Uninterpreted function returning Entity (infinite Herbrand universe)
            "(set-logic ALL)\n(declare-sort Entity 0)\n(declare-fun next_e (Entity) Entity)\n(check-sat)",
            // String concatenation (unsupported String operation)
            "(set-logic ALL)\n(declare-const s String)\n(assert (= (str.++ s \"a\") \"ba\"))\n(check-sat)",
        ];

        let backend = crate::smt::BilSmtSolver;
        assert_eq!(backend.name(), "bil-smt");
        for script in cases {
            assert!(
                instantiate_entity_quantifiers(script).is_err(),
                "expected script to be rejected from fragment:\n{}",
                script
            );
            let res = backend.check(script);
            assert_eq!(res.prover, "bil-smt");
            assert_eq!(
                res.verdict,
                Verdict::Unknown,
                "outside fragment must return Unknown, never a guess: {:?}",
                res
            );
            assert!(res.detail.contains("outside bil-smt fragment"), "{}", res.detail);
        }

        // Valid fragment script now decides SAT / UNSAT in 8.1.3
        let valid = "(set-logic ALL)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n";
        let res = run_smt_prover(Prover::BilSmt, valid);
        assert_eq!(res.prover, "bil-smt");
        assert_eq!(res.verdict, Verdict::Consistent);
    }

    #[test]
    fn repo_wide_soundness_gate_matches_z3_on_all_examples_and_tests() {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(repo_wide_soundness_gate_inner)
            .unwrap()
            .join()
            .unwrap();
    }

    fn repo_wide_soundness_gate_inner() {
        let has_z3 = find_solver_binary("z3").is_some();

        let mut sources: Vec<(String, String)> = Vec::new();
        for dir in ["examples", "examples/domains", "examples/domains/seeded_bugs"] {
            let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
                .unwrap()
                .map(|e| e.unwrap().path())
                .filter(|p| p.extension().is_some_and(|x| x == "bil"))
                .collect();
            files.sort();
            for path in files {
                let src = std::fs::read_to_string(&path).unwrap();
                sources.push((path.display().to_string(), src));
            }
        }

        // Inline test programs used across tests/*.rs
        let inline_programs: &[(&str, &str)] = &[
            (
                "tests/cli.rs::SMT_ONLY_REFUTABLE",
                r#"
                fn sq(x: Int) -> Int
                  requires x * x == 1369
                  ensures  result == 0
                =
                  if true -> 0 - x fi
                "#,
            ),
            (
                "tests/cli.rs::linear_smt_only_refutable",
                r#"
                fn linear_smt_only(a: Int, b: Int) -> Int
                  requires a == 37 && b == -73
                  ensures  result == 0
                =
                  if true -> a + b fi
                "#,
            ),
            (
                "tests/soundness.rs::bogus_and_bad",
                r#"
                proof bogus()
                  requires true
                  ensures  false
                {
                  true
                }
                fn bad(x: Int) -> Int
                  requires x > 0
                  ensures  result < 0
                =
                  x
                "#,
            ),
            (
                "tests/soundness.rs::vacuous_src",
                r#"
                concept Tank { level: Int, cap: Int }
                axiom A1: forall t in Tank : t.level > t.cap
                axiom A2: forall t in Tank : t.cap >= t.level
                fn impossible(t: Tank) -> Int
                  requires t.level >= 0
                  ensures  result < 0
                =
                  t.level
                "#,
            ),
            (
                "tests/soundness.rs::missed_by_bounded_src",
                r#"
                fn sneaky(x: Int) -> Int
                  requires x == 7
                  ensures  result == 0
                =
                  x
                "#,
            ),
            (
                "tests/soundness.rs::euclid_div_mod",
                r#"
                proof euclid_mod()
                  requires true
                  ensures  (-7) % 2 == 1 && (-7) / 2 == -4
                {
                  true
                }
                fn neg_mod(x: Int) -> Int
                  requires x == -7
                  ensures  result == 1
                =
                  x % 2
                fn neg_div(x: Int) -> Int
                  requires x == -7
                  ensures  result == -4
                =
                  x / 2
                "#,
            ),
            (
                "tests/soundness.rs::nested_do_od_and_threshold",
                r#"
                fn countdown(n: Int) -> Int
                  requires n >= 0
                  ensures  result == 0
                =
                  let start = n in
                  do c = start
                    invariant c >= 0
                    variant c
                    c > 0 -> c := c - 1
                  od then c

                fn buggy_threshold(x: Int) -> Int
                  requires x >= 0
                  ensures  result > 0
                =
                  if x == 4321 -> 0
                  [] x != 4321 -> 1
                  fi
                "#,
            ),
            (
                "tests/soundness.rs::bmc_counters",
                r#"
                system BoundedCounter {
                    state count: Int = 0
                    state locked: Bool = false
                    invariant CountWithinBounds:
                        count >= 0 && count <= 3
                    transition
                        !locked && count < 3 -> count := count + 1
                    []  !locked && count == 3 -> locked := true
                    []  locked && count > 0 -> count := count - 1
                    []  locked && count == 0 -> locked := false
                }
                system OverflowCounter {
                    state count: Int = 0
                    invariant MaxTwo:
                        count <= 2
                    transition
                        count < 5 -> count := count + 1
                    []  count >= 5 -> count := 0
                }
                "#,
            ),
            (
                "tests/timed_guards.rs::met_and_late",
                r#"
                system EpiMet {
                  state detected: Bool = false
                  state heater_off: Bool = false
                  state wait: Int = 0
                  clock scan period 1ms
                  deadline Cut: detected => heater_off within 3ms
                  terminal heater_off
                  transition
                     !detected               -> detected := true
                  [] detected && wait < 2    -> wait := wait + 1
                  [] detected && wait >= 2   -> heater_off := true
                }
                system EpiLate {
                  state detected: Bool = false
                  state heater_off: Bool = false
                  state wait: Int = 0
                  clock scan period 1ms
                  deadline Cut: detected => heater_off within 3ms
                  terminal heater_off
                  transition
                     !detected               -> detected := true
                  [] detected && wait < 3    -> wait := wait + 1
                  [] detected && wait >= 3   -> heater_off := true
                }
                "#,
            ),
            (
                "tests/differential.rs::gcl_and_edge_cases",
                r#"
                fn abs_val(x: Int) -> Int
                    ensures result >= 0
                = if
                    x >= 0 -> x
                    [] x < 0 -> -x
                  fi

                fn count_down(n: Int) -> Int
                    requires n >= 0
                    ensures result == 0
                = do r = n
                    invariant r >= 0
                    variant r
                    r > 0 -> r := r - 1
                  od then r

                fn loop_collatz_steps(n: Int) -> Int
                    requires n >= 1
                    ensures result >= 0
                =
                    do cur = n, steps = 0
                        invariant cur >= 1 && steps >= 0
                        variant cur
                    :
                        cur > 1 && cur % 2 == 0 -> cur := cur / 2, steps := steps + 1
                    [] cur > 1 && cur % 2 != 0 -> cur := cur - 1, steps := steps + 1
                    od
                    then steps
                "#,
            ),
            (
                "tests/security.rs::keyword_fn",
                r#"
                fn unsafe(self: Int) -> Int
                  requires self >= 0
                  ensures result == self + 1
                =
                  self + 1
                "#,
            ),
        ];
        for (label, src) in inline_programs {
            sources.push(((*label).to_string(), (*src).to_string()));
        }

        // Collect all individual SMT-LIB2 queries: (label, script)
        let mut all_queries: Vec<(String, String)> = Vec::new();
        let mut incremental_batches_checked = 0usize;

        for (label, src) in &sources {
            let session = CompilationSession::from_source(src)
                .unwrap_or_else(|e| panic!("{}: failed to compile: {}", label, e));

            // 1. Ontology consistency query when axioms or concepts exist
            let has_axioms = session
                .program
                .items
                .iter()
                .any(|i| matches!(i, crate::ast::Item::Axiom(_)));
            if has_axioms || !session.ontology.concepts.is_empty() {
                let ont_smt2 =
                    emit_ontology_consistency_smt2(&session.program, &session.ontology);
                all_queries.push((format!("{}::ontology_consistency", label), ont_smt2));
            }

            // 2. All concept pair subsumption queries
            let concept_names: Vec<&String> = session.ontology.concepts.keys().collect();
            for &c1 in &concept_names {
                for &c2 in &concept_names {
                    if c1 != c2 {
                        let sub_smt2 =
                            emit_subsumption_smt2(&session.program, &session.ontology, c1, c2);
                        all_queries.push((
                            format!("{}::subsumption({}<:{})", label, c1, c2),
                            sub_smt2,
                        ));
                    }
                }
            }

            // 3. All WP verification obligation scripts
            let obs = generate_obligations(&session.program, &session.ontology);
            for ob in &obs {
                if let Some(script) = &ob.smt2_script {
                    all_queries.push((
                        format!("{}::vc::{} ({})", label, ob.fn_name, ob.kind),
                        script.clone(),
                    ));
                }
            }

            // 4. Incremental (push 1)/(pop 1) batch for multi-obligation functions
            let mut fn_groups: BTreeMap<String, Vec<String>> = BTreeMap::new();
            for ob in &obs {
                if let Some(script) = &ob.smt2_script {
                    fn_groups
                        .entry(ob.fn_name.clone())
                        .or_default()
                        .push(script.clone());
                }
            }
            for (fn_name, scripts) in fn_groups {
                if scripts.len() < 2 {
                    continue;
                }
                let last_script = scripts.last().unwrap();
                let Some((header, _)) = last_script.split_once(";; Refutation of VC:") else {
                    continue;
                };
                let mut refutations = Vec::with_capacity(scripts.len());
                for sc in &scripts {
                    if let Some((_, tail)) = sc.split_once(";; Refutation of VC:") {
                        if let Some(assert_line) =
                            tail.lines().find(|l| l.starts_with("(assert (not "))
                        {
                            let inner = assert_line
                                .strip_prefix("(assert ")
                                .and_then(|s| s.strip_suffix(')'))
                                .unwrap();
                            refutations.push(inner.to_string());
                        }
                    }
                }
                if refutations.len() == scripts.len()
                    && scripts
                        .iter()
                        .all(|sc| instantiate_entity_quantifiers(sc).is_ok())
                {
                    let (_, bil_verdicts) = run_smt_incremental_batch_with_prover(
                        Prover::BilSmt,
                        header,
                        &refutations,
                    )
                    .unwrap_or_else(|| {
                        panic!(
                            "{}::{}: expected bil-smt incremental batch to succeed",
                            label, fn_name
                        )
                    });
                    for (sc, inc_v) in scripts.iter().zip(&bil_verdicts) {
                        let single_v = run_bil_smt(sc).verdict;
                        assert_eq!(
                            *inc_v, single_v,
                            "{}::{}: incremental push/pop verdict differed from standalone verdict",
                            label, fn_name
                        );
                    }
                    incremental_batches_checked += 1;
                }
            }

            // 5. Symbolic BMC queries for k = 1..=6 on every system block
            for item in &session.program.items {
                if let crate::ast::Item::System(sys) = item {
                    for k in 1..=6 {
                        if let Some(bmc_smt2) =
                            emit_symbolic_bmc_smt2(sys, &session.ontology, k)
                        {
                            all_queries.push((
                                format!("{}::bmc::{} (k={})", label, sys.name, k),
                                bmc_smt2,
                            ));
                        }
                    }
                }
            }
        }

        let mut in_fragment_count = 0usize;
        let mut out_of_fragment_count = 0usize;
        let mut z3_batch = String::new();
        let mut z3_checks: Vec<(String, Verdict, bool)> = Vec::new();

        for (q_label, script) in &all_queries {
            let in_fragment = instantiate_entity_quantifiers(script).is_ok();
            let bil_res = run_bil_smt(script);

            if in_fragment {
                in_fragment_count += 1;
                // Soundness Invariant 2: Every in-fragment repo query must produce a definitive verdict
                assert!(
                    matches!(bil_res.verdict, Verdict::Consistent | Verdict::Inconsistent),
                    "{}: in-fragment query returned non-definitive verdict {:?}\n{}",
                    q_label,
                    bil_res,
                    script
                );
            } else {
                out_of_fragment_count += 1;
                // Soundness Invariant 3: Out-of-fragment queries must return Unknown, never a guess
                assert_eq!(
                    bil_res.verdict,
                    Verdict::Unknown,
                    "{}: out-of-fragment query must return Unknown, got {:?}\n{}",
                    q_label,
                    bil_res,
                    script
                );
            }

            if has_z3 {
                z3_batch.push_str("(reset)\n");
                z3_batch.push_str(script);
                z3_checks.push((q_label.clone(), bil_res.verdict, in_fragment));
            }
        }

        assert!(
            in_fragment_count >= 450,
            "expected >= 450 in-fragment repo queries, got {}",
            in_fragment_count
        );
        assert!(
            out_of_fragment_count >= 5,
            "expected >= 5 out-of-fragment repo queries (e.g. recursive_contracts, gcd_refinement, SMT_ONLY_REFUTABLE), got {}",
            out_of_fragment_count
        );
        assert!(incremental_batches_checked >= 20);

        if has_z3 {
            let z3_res = run_smt_prover(Prover::Z3, &z3_batch);
            let z3_verdicts: Vec<Verdict> = z3_res
                .stdout
                .lines()
                .map(str::trim)
                .filter_map(|l| match l {
                    "sat" => Some(Verdict::Consistent),
                    "unsat" => Some(Verdict::Inconsistent),
                    "unknown" => Some(Verdict::Unknown),
                    _ => None,
                })
                .collect();
            assert_eq!(
                z3_verdicts.len(),
                z3_checks.len(),
                "expected {} z3 verdicts from batch, got {}",
                z3_checks.len(),
                z3_verdicts.len()
            );

            for ((q_label, bil_v, in_fragment), z3_v) in z3_checks.iter().zip(z3_verdicts) {
                // Soundness Invariant 1: bil-smt must NEVER disagree with z3 (never SAT when z3 says UNSAT, never UNSAT when z3 says SAT)
                let disagreed = (*bil_v == Verdict::Consistent && z3_v == Verdict::Inconsistent)
                    || (*bil_v == Verdict::Inconsistent && z3_v == Verdict::Consistent);
                assert!(
                    !disagreed,
                    "CRITICAL SOUNDNESS DISAGREEMENT on {}: bil-smt returned {:?} while z3 returned {:?}",
                    q_label,
                    bil_v,
                    z3_v
                );
                if *in_fragment {
                    assert_eq!(
                        *bil_v, z3_v,
                        "In-fragment query {} mismatch: bil-smt returned {:?} while z3 returned {:?}",
                        q_label, bil_v, z3_v
                    );
                }
            }
        }
    }
}
