//! Fragment classifier, finite `Entity` quantifier instantiator, and interface for the in-repo
//! `bil-smt` backend (Roadmap 8.1.2).
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
//!    and `(get-model)` (ignored or handled by the solver).
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
//! `QF_UFLIA` script (or pure `QF_LIA` after Ackermannization / constant specialization when all
//! `Entity` arguments are ground constants).
//!
//! In 8.1.2, `run_bil_smt` validates that the input script is in this fragment, performs the finite
//! `Entity` instantiation, and returns `Verdict::Unknown` (never a guess; decision procedure is 8.1.3).

use crate::smt::{parse_sexprs, ProverResult, SExpr, Verdict};
use std::collections::{BTreeMap, BTreeSet};

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
    let mut out_lines = Vec::new();
    let mut scope = Scope::default();
    let mut stack: Vec<Scope> = Vec::new();
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
                    if sort == SmtSort::Entity && !scope.entity_consts.contains(name) {
                        scope.entity_consts.push(name.clone());
                    }
                    scope.consts.insert(name.clone(), sort);
                }
                out_lines.push(render_sexpr(form));
            }
            "define-const" => {
                if let (SExpr::Atom(name), _, val_expr) = (&items[1], &items[2], &items[3]) {
                    let k = eval_const_int(val_expr, &scope.defined_ints).unwrap();
                    scope.consts.insert(name.clone(), SmtSort::Int);
                    scope.defined_ints.insert(name.clone(), k);
                }
                out_lines.push(render_sexpr(form));
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
                out_lines.push(render_sexpr(form));
            }
            "push" => {
                stack.push(scope.clone());
                out_lines.push(render_sexpr(form));
            }
            "pop" => {
                if let Some(prev) = stack.pop() {
                    scope = prev;
                }
                out_lines.push(render_sexpr(form));
            }
            "assert" => {
                if uses_entity_quantifier && scope.entity_consts.is_empty() && !injected_witness {
                    let witness = "__entity_witness".to_string();
                    out_lines.push(format!("(declare-const {} Entity)", witness));
                    scope.entity_consts.push(witness.clone());
                    scope.consts.insert(witness, SmtSort::Entity);
                    injected_witness = true;
                }
                let expanded = expand_quantifiers(&items[1], &scope.entity_consts, &BTreeMap::new());
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

/// Entry point for the in-repo `bil-smt` backend behind `--prover bil-smt`.
///
/// In Roadmap 8.1.2, this validates that `smt2_input` falls inside the decidable fragment and
/// expands universal `Entity` quantifiers, returning `Verdict::Unknown` (never a guess) both
/// outside the fragment and while the 8.1.3 decision procedure is not yet wired in.
pub fn run_bil_smt(smt2_input: &str) -> ProverResult {
    match instantiate_entity_quantifiers(smt2_input) {
        Ok(_qf_script) => ProverResult {
            prover: "bil-smt".to_string(),
            verdict: Verdict::Unknown,
            stdout: "unknown\n".to_string(),
            stderr: String::new(),
            elapsed_ms: 0,
            detail: "bil-smt fragment accepted (decision procedure pending 8.1.3)".to_string(),
        },
        Err(reason) => ProverResult {
            prover: "bil-smt".to_string(),
            verdict: Verdict::Unknown,
            stdout: "unknown\n".to_string(),
            stderr: String::new(),
            elapsed_ms: 0,
            detail: format!("outside bil-smt fragment: {}", reason),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::{
        emit_ontology_consistency_smt2, find_solver_binary, run_smt_prover, Prover, SolverBackend,
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
    fn every_domain_example_vc_is_in_fragment_and_instantiation_matches_z3() {
        let has_z3 = find_solver_binary("z3").is_some();
        let files = domain_files();
        assert_eq!(files.len(), 14);
        let mut total_obligations = 0usize;
        let mut quantified_obligations = 0usize;
        let mut z3_batch = String::new();
        let mut expected_verdicts: Vec<(String, &'static str)> = Vec::new();

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
                assert!(
                    !qf.contains("(forall"),
                    "{}: instantiated ontology script still has forall:\n{}",
                    path.display(),
                    qf
                );
                if has_z3 {
                    z3_batch.push_str("(reset)\n");
                    z3_batch.push_str(&ont_smt2);
                    z3_batch.push_str("(reset)\n");
                    z3_batch.push_str(&qf);
                    expected_verdicts.push((format!("{}::ontology", path.display()), "sat"));
                }
            }

            // 2. Check every VC obligation script
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
                assert!(
                    !qf.contains("(forall"),
                    "{}::{}: instantiated script still contains forall:\n{}",
                    path.display(),
                    ob.fn_name,
                    qf
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
    }

    #[test]
    fn seeded_bug_refutation_is_preserved_under_entity_instantiation() {
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
        let qf = instantiate_entity_quantifiers(script).expect("in fragment");
        if find_solver_binary("z3").is_some() {
            let orig_res = run_smt_prover(Prover::Z3, script);
            let qf_res = run_smt_prover(Prover::Z3, &qf);
            assert_eq!(orig_res.verdict, Verdict::Consistent);
            assert_eq!(qf_res.verdict, Verdict::Consistent);
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

        // Valid fragment script also returns Unknown in 8.1.2 (decision procedure is 8.1.3)
        let valid = "(set-logic ALL)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n";
        let res = run_smt_prover(Prover::BilSmt, valid);
        assert_eq!(res.prover, "bil-smt");
        assert_eq!(res.verdict, Verdict::Unknown);
        assert!(res.detail.contains("fragment accepted"), "{}", res.detail);
    }
}

