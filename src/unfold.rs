//! Unfolds calls to user-defined functions inside a Verification Condition so the SMT encoding can
//! reason about them. Each call `f(a)` is replaced by `f`'s body with `a` substituted for its
//! parameters, and the VC is strengthened with the checks the interpreter performs on every call:
//! `f`'s `requires` (and a refined spec's) must hold on entry and its `ensures` on exit. Those
//! checks are guarded by the short-circuit context of the call, matching `eval.rs`.
//!
//! A recursive call is not unfolded again. If the callee declares a `variant`, the call is replaced
//! by a fresh value that is assumed to satisfy the callee's `ensures`, after checking its `requires`
//! and that the variant is non-negative and strictly smaller than at the enclosing activation of
//! the same function. That is the usual inductive argument: the variant bounds every call chain,
//! and the callee's own contract obligation proves the `ensures` it assumes.
//!
//! An `if..fi` in a position whose type is known (a function body, possibly under `let`s) gets a
//! fresh value assumed equal to the body of some branch whose guard holds, so the VC must hold for
//! every enabled branch, as Dijkstra's nondeterministic choice requires.
//!
//! Every assumption is guarded by the checks that make it satisfiable (a guard holds, or the
//! callee's `requires` and the variant check hold), so a failed check can never be hidden by a
//! false hypothesis.

use crate::ast::{BinOp, Expr, FnDecl, GclBody, Item, Program, SpecDecl, TypeExpr, UnaryOp};
use crate::builtins::BuiltinFn;
use crate::expr_utils::subst_expr;
use std::collections::BTreeMap;

/// Deepest chain of nested user calls that is unfolded before giving up.
const MAX_DEPTH: usize = 16;

/// A VC with its user calls unfolded. `expr` mentions the `fresh` variables free; the VC holds iff
/// `expr` holds for every value of them.
#[derive(Debug, Clone, PartialEq)]
pub struct Unfolded {
    pub expr: Expr,
    pub fresh: Vec<(String, TypeExpr)>,
}

/// Returns `vc` with every user-defined call unfolded, conjoined with the call-site contract checks.
/// Returns `None` when a call cannot be unfolded (recursion without a `variant`, too deep, or a
/// call under a quantifier whose checks cannot be expressed), leaving the obligation to the bounded
/// checker.
pub fn unfold_user_calls(program: &Program, vc: &Expr) -> Option<Unfolded> {
    let mut u = Unfolder {
        fns: BTreeMap::new(),
        specs: BTreeMap::new(),
        stack: Vec::new(),
        fresh: Vec::new(),
    };
    for item in &program.items {
        match item {
            Item::FnDecl(f) => {
                u.fns.insert(f.name.as_str(), f);
            }
            Item::Spec(s) => {
                u.specs.insert(s.name.as_str(), s);
            }
            _ => {}
        }
    }
    if u.fns.is_empty() {
        return Some(Unfolded {
            expr: vc.clone(),
            fresh: Vec::new(),
        });
    }
    let p = u.go(vc, None)?;
    Some(Unfolded {
        expr: implies(p.assume, conj(p.safe, p.value)),
        fresh: u.fresh,
    })
}

/// One unfolded expression: its `value`, the condition `safe` under which evaluating it raises no
/// contract violation, and the facts `assume` that define the fresh variables it introduced.
struct Part {
    value: Expr,
    safe: Expr,
    assume: Expr,
}

impl Part {
    fn pure(value: Expr) -> Part {
        Part {
            value,
            safe: Expr::Bool(true),
            assume: Expr::Bool(true),
        }
    }
}

struct Unfolder<'a> {
    fns: BTreeMap<&'a str, &'a FnDecl>,
    specs: BTreeMap<&'a str, &'a SpecDecl>,
    /// Active unfoldings, innermost last, with each one's parameter-to-argument map.
    stack: Vec<(&'a str, BTreeMap<String, Expr>)>,
    fresh: Vec<(String, TypeExpr)>,
}

impl<'a> Unfolder<'a> {
    /// Unfolds `e`. `ty` is its type when known, which an `if..fi` needs for its fresh value.
    fn go(&mut self, e: &Expr, ty: Option<&TypeExpr>) -> Option<Part> {
        match e {
            Expr::Unary { op, expr } => {
                let p = self.go(expr, None)?;
                Some(Part {
                    value: Expr::Unary {
                        op: *op,
                        expr: Box::new(p.value),
                    },
                    ..p
                })
            }
            Expr::Binary { op, left, right } => {
                let l = self.go(left, None)?;
                let r = self.go(right, None)?;
                // The right operand of `&&`, `=>` and `||` is evaluated only when the left one
                // does not decide the result.
                let guard = match op {
                    BinOp::And | BinOp::Implies => Some(l.value.clone()),
                    BinOp::Or => Some(not(l.value.clone())),
                    _ => None,
                };
                let (safe, assume) = match guard {
                    Some(g) => (
                        conj(l.safe, implies(g.clone(), r.safe)),
                        conj(l.assume, implies(g, r.assume)),
                    ),
                    None => (conj(l.safe, r.safe), conj(l.assume, r.assume)),
                };
                Some(Part {
                    value: bin(*op, l.value, r.value),
                    safe,
                    assume,
                })
            }
            Expr::FieldAccess { base, field } => {
                let p = self.go(base, None)?;
                Some(Part {
                    value: Expr::FieldAccess {
                        base: Box::new(p.value),
                        field: field.clone(),
                    },
                    ..p
                })
            }
            Expr::LetIn { name, value, body } => {
                let v = self.go(value, None)?;
                let b = self.go(body, ty)?;
                let let_in = |x: Expr| {
                    if x == Expr::Bool(true) {
                        x
                    } else {
                        Expr::LetIn {
                            name: name.clone(),
                            value: Box::new(v.value.clone()),
                            body: Box::new(x),
                        }
                    }
                };
                Some(Part {
                    safe: conj(v.safe.clone(), let_in(b.safe)),
                    assume: conj(v.assume.clone(), let_in(b.assume)),
                    value: let_in(b.value),
                })
            }
            Expr::Quantifier {
                kind,
                var,
                domain,
                body,
            } => {
                let d = self.go(domain, None)?;
                let b = self.go(body, None)?;
                if b.safe != Expr::Bool(true) || b.assume != Expr::Bool(true) {
                    return None;
                }
                Some(Part {
                    value: Expr::Quantifier {
                        kind: kind.clone(),
                        var: var.clone(),
                        domain: Box::new(d.value),
                        body: Box::new(b.value),
                    },
                    ..d
                })
            }
            Expr::IfFi { branches } => {
                let ty = ty?;
                let r = self.fresh_var("if", ty);
                // All guards are evaluated first; at least one must hold.
                let mut safe = Expr::Bool(true);
                let mut assume = Expr::Bool(true);
                let mut any = Expr::Bool(false);
                let mut choice = Expr::Bool(false);
                let mut guarded = Vec::with_capacity(branches.len());
                for br in branches {
                    let g = self.go(&br.guard, None)?;
                    safe = conj(safe, g.safe);
                    assume = conj(assume, g.assume);
                    any = disj(any, g.value.clone());
                    guarded.push(g.value);
                }
                safe = conj(safe, any.clone());
                for (br, g) in branches.iter().zip(guarded) {
                    match &br.body {
                        GclBody::Expr(body) => {
                            let b = self.go(body, Some(ty))?;
                            safe = conj(safe, implies(g.clone(), b.safe));
                            assume = conj(assume, implies(g.clone(), b.assume));
                            choice = disj(choice, conj(g, bin(BinOp::Eq, r.clone(), b.value)));
                        }
                        GclBody::Abort => safe = conj(safe, not(g)),
                        GclBody::Skip | GclBody::Updates(_) => return None,
                    }
                }
                Some(Part {
                    value: r,
                    safe,
                    assume: conj(assume, implies(any, choice)),
                })
            }
            Expr::Call { func, args } => {
                let mut arg_vals = Vec::with_capacity(args.len());
                let mut safe = Expr::Bool(true);
                let mut assume = Expr::Bool(true);
                for a in args {
                    let p = self.go(a, None)?;
                    arg_vals.push(p.value);
                    safe = conj(safe, p.safe);
                    assume = conj(assume, p.assume);
                }
                let callee = match self.fns.get(func.as_str()) {
                    Some(f) if BuiltinFn::from_name(func).is_none() => *f,
                    _ => {
                        let call = Expr::Call {
                            func: func.clone(),
                            args: arg_vals,
                        };
                        return Some(Part {
                            value: call,
                            safe,
                            assume,
                        });
                    }
                };
                let recursive = self.stack.iter().any(|(n, _)| *n == callee.name);
                let p = if recursive {
                    self.abstract_call(callee, &arg_vals)?
                } else if self.stack.len() >= MAX_DEPTH {
                    return None;
                } else {
                    self.unfold_call(callee, &arg_vals)?
                };
                Some(Part {
                    value: p.value,
                    safe: conj(safe, p.safe),
                    assume: conj(assume, p.assume),
                })
            }
            // Literals and variables need no unfolding. Forms the SMT encoding rejects anyway
            // (`do..od`, `match`, records, lists) are left as-is.
            _ => Some(Part::pure(e.clone())),
        }
    }

    fn fresh_var(&mut self, what: &str, ty: &TypeExpr) -> Expr {
        // `-` cannot appear in a bil identifier, so these never clash with program names.
        let name = format!("{}-{}", what, self.fresh.len() + 1);
        self.fresh.push((name.clone(), ty.clone()));
        Expr::Var(name)
    }

    /// Contract checks of a call: `f`'s requires and a refined spec's, then (on exit) its ensures
    /// and the spec's, each with parameters (and `result`) substituted.
    fn contract(&self, f: &FnDecl, args: &[Expr], result: &Expr) -> (Vec<Expr>, Vec<Expr>) {
        let map = param_map(f.params.iter().map(|p| &p.name), args);
        let spec = f
            .refines
            .as_deref()
            .and_then(|s| self.specs.get(s).copied());
        let spec_map = spec
            .map(|s| param_map(s.params.iter().map(|p| &p.name), args))
            .unwrap_or_default();
        let with_result = |m: &BTreeMap<String, Expr>| {
            let mut m = m.clone();
            m.insert("result".into(), result.clone());
            m
        };
        let mut pre = Vec::new();
        let mut post = Vec::new();
        if let Some(req) = &f.requires {
            pre.push(subst_expr(req, &map));
        }
        if let Some(sreq) = spec.and_then(|s| s.requires.as_ref()) {
            pre.push(subst_expr(sreq, &spec_map));
        }
        if let Some(ens) = &f.ensures {
            post.push(subst_expr(ens, &with_result(&map)));
        }
        if let Some(sens) = spec.and_then(|s| s.ensures.as_ref()) {
            post.push(subst_expr(sens, &with_result(&spec_map)));
        }
        (pre, post)
    }

    /// Unfolds `checks` in order, each one required to hold.
    fn check_all(&mut self, checks: Vec<Expr>, part: &mut Part) -> Option<()> {
        for c in checks {
            let p = self.go(&c, None)?;
            part.safe = conj(part.safe.clone(), conj(p.safe, p.value));
            part.assume = conj(part.assume.clone(), p.assume);
        }
        Some(())
    }

    /// Unfolds one call of `f` on already-unfolded `args`, in the order `eval.rs` checks it:
    /// requires, refined spec requires, body, ensures, refined spec ensures.
    fn unfold_call(&mut self, f: &'a FnDecl, args: &[Expr]) -> Option<Part> {
        let map = param_map(f.params.iter().map(|p| &p.name), args);
        self.stack.push((f.name.as_str(), map.clone()));
        let mut part = Part::pure(Expr::Bool(true));
        let (pre, _) = self.contract(f, args, &Expr::Bool(true));
        self.check_all(pre, &mut part)?;
        let body = self.go(&subst_expr(&f.body, &map), Some(&f.ret_ty))?;
        part.safe = conj(part.safe, body.safe);
        part.assume = conj(part.assume, body.assume);
        let (_, post) = self.contract(f, args, &body.value);
        self.check_all(post, &mut part)?;
        self.stack.pop();
        part.value = body.value;
        Some(part)
    }

    /// Replaces a recursive call of `f` by a fresh value satisfying `f`'s ensures, after checking
    /// its requires and that `f`'s variant decreases from the enclosing activation of `f`.
    fn abstract_call(&mut self, f: &'a FnDecl, args: &[Expr]) -> Option<Part> {
        let variant = f.variant.as_ref()?;
        let outer = &self.stack.iter().rev().find(|(n, _)| *n == f.name)?.1;
        let before = subst_expr(variant, outer);
        let after = subst_expr(variant, &param_map(f.params.iter().map(|p| &p.name), args));
        let decreases = conj(
            bin(BinOp::Le, Expr::Int(0), before.clone()),
            bin(BinOp::Lt, after, before),
        );

        let result = self.fresh_var(&format!("ret-{}", f.name), &f.ret_ty);
        let (mut pre, post) = self.contract(f, args, &result);
        pre.push(decreases);
        let mut part = Part::pure(result);
        let mut entry = Expr::Bool(true);
        for c in pre {
            let p = self.go(&c, None)?;
            part.safe = conj(part.safe, conj(p.safe, p.value.clone()));
            part.assume = conj(part.assume, p.assume);
            entry = conj(entry, p.value);
        }
        // The ensures is assumed, not checked: the callee's own obligation proves it.
        let mut exit = Expr::Bool(true);
        for c in post {
            let p = self.go(&c, None)?;
            exit = conj(exit, conj(p.assume, p.value));
        }
        part.assume = conj(part.assume, implies(entry, exit));
        Some(part)
    }
}

fn param_map<'n>(names: impl Iterator<Item = &'n String>, args: &[Expr]) -> BTreeMap<String, Expr> {
    names.cloned().zip(args.iter().cloned()).collect()
}

fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::Binary {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}

fn conj(a: Expr, b: Expr) -> Expr {
    match (&a, &b) {
        (Expr::Bool(true), _) => b,
        (_, Expr::Bool(true)) => a,
        _ => bin(BinOp::And, a, b),
    }
}

fn implies(a: Expr, b: Expr) -> Expr {
    if b == Expr::Bool(true) || a == Expr::Bool(true) {
        return b;
    }
    bin(BinOp::Implies, a, b)
}

fn disj(a: Expr, b: Expr) -> Expr {
    match (&a, &b) {
        (Expr::Bool(false), _) => b,
        (_, Expr::Bool(false)) => a,
        _ => bin(BinOp::Or, a, b),
    }
}

fn not(a: Expr) -> Expr {
    Expr::Unary {
        op: UnaryOp::Not,
        expr: Box::new(a),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn program(src: &str) -> Program {
        crate::parse_source(src).expect("parse")
    }

    #[test]
    fn unfolds_call_and_adds_contract_checks() {
        let p = program(
            "fn dbl(x: Int) -> Int requires x >= 0 ensures result >= x = x + x\n\
             fn quad(y: Int) -> Int requires y >= 0 ensures result >= 0 = dbl(dbl(y))\n",
        );
        let vc = Expr::Call {
            func: "quad".into(),
            args: vec![Expr::Var("n".into())],
        };
        let out = crate::expr_utils::format_expr_concise(&unfold_user_calls(&p, &vc).unwrap().expr);
        assert!(!out.contains("dbl(") && !out.contains("quad("), "{out}");
        assert!(out.contains("n >= 0"), "callee requires must be checked: {out}");
    }

    #[test]
    fn recursion_is_not_unfolded() {
        let p = program("fn f(x: Int) -> Int = f(x)\n");
        let vc = Expr::Call {
            func: "f".into(),
            args: vec![Expr::Int(1)],
        };
        assert_eq!(unfold_user_calls(&p, &vc), None);
    }

    #[test]
    fn checks_after_short_circuit_are_guarded() {
        let p = program("fn pos(x: Int) -> Bool requires x > 0 = x > 0\n");
        // `b && pos(x)` only calls `pos` when `b` holds.
        let vc = bin(
            BinOp::And,
            Expr::Var("b".into()),
            Expr::Call {
                func: "pos".into(),
                args: vec![Expr::Var("x".into())],
            },
        );
        let out = unfold_user_calls(&p, &vc).unwrap();
        let s = crate::expr_utils::format_expr_concise(&out.expr);
        assert!(s.contains("b => "), "{s}");
    }

    #[test]
    fn recursive_call_uses_contract_only_with_a_variant() {
        let body = "if n == 0 -> 0 [] n > 0 -> f(n - 1) fi";
        let call = Expr::Call {
            func: "f".into(),
            args: vec![Expr::Var("m".into())],
        };
        let without = program(&format!(
            "fn f(n: Int) -> Int requires n >= 0 ensures result >= 0 = {body}\n"
        ));
        assert_eq!(unfold_user_calls(&without, &call), None);

        let with = program(&format!(
            "fn f(n: Int) -> Int requires n >= 0 ensures result >= 0 variant n = {body}\n"
        ));
        let out = unfold_user_calls(&with, &call).unwrap();
        let names: Vec<&str> = out.fresh.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["if-1", "ret-f-2"]);
        let s = crate::expr_utils::format_expr_concise(&out.expr);
        // The variant check compares the inner call with the unfolded activation.
        assert!(s.contains("(0 <= m)") && s.contains("((m - 1) < m)"), "{s}");
    }
}
