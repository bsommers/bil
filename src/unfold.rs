//! Unfolds calls to user-defined functions inside a Verification Condition so the SMT encoding can
//! reason about them. Each call `f(a)` is replaced by `f`'s body with `a` substituted for its
//! parameters, and the VC is strengthened with the checks the interpreter performs on every call:
//! `f`'s `requires` (and a refined spec's) must hold on entry and its `ensures` on exit. Those
//! checks are guarded by the short-circuit context of the call, matching `eval.rs`.

use crate::ast::{BinOp, Expr, FnDecl, Item, Program, SpecDecl, UnaryOp};
use crate::builtins::BuiltinFn;
use crate::expr_utils::subst_expr;
use std::collections::BTreeMap;

/// Deepest chain of nested user calls that is unfolded before giving up.
const MAX_DEPTH: usize = 16;

/// Returns `vc` with every user-defined call unfolded, conjoined with the call-site contract checks.
/// Returns `None` when a call cannot be unfolded (recursion, too deep, or a call under a quantifier
/// whose checks cannot be expressed), leaving the obligation to the bounded checker.
pub fn unfold_user_calls(program: &Program, vc: &Expr) -> Option<Expr> {
    let mut u = Unfolder {
        fns: BTreeMap::new(),
        specs: BTreeMap::new(),
        stack: Vec::new(),
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
        return Some(vc.clone());
    }
    let (value, safe) = u.go(vc)?;
    Some(conj(safe, value))
}

struct Unfolder<'a> {
    fns: BTreeMap<&'a str, &'a FnDecl>,
    specs: BTreeMap<&'a str, &'a SpecDecl>,
    stack: Vec<&'a str>,
}

impl<'a> Unfolder<'a> {
    /// Returns the unfolded expression and the condition under which evaluating it raises no
    /// contract violation.
    fn go(&mut self, e: &Expr) -> Option<(Expr, Expr)> {
        match e {
            Expr::Unary { op, expr } => {
                let (v, s) = self.go(expr)?;
                Some((
                    Expr::Unary {
                        op: *op,
                        expr: Box::new(v),
                    },
                    s,
                ))
            }
            Expr::Binary { op, left, right } => {
                let (lv, ls) = self.go(left)?;
                let (rv, rs) = self.go(right)?;
                let safe = match op {
                    BinOp::And | BinOp::Implies => conj(ls, implies(lv.clone(), rs)),
                    BinOp::Or => conj(ls, implies(not(lv.clone()), rs)),
                    _ => conj(ls, rs),
                };
                Some((bin(*op, lv, rv), safe))
            }
            Expr::FieldAccess { base, field } => {
                let (v, s) = self.go(base)?;
                Some((
                    Expr::FieldAccess {
                        base: Box::new(v),
                        field: field.clone(),
                    },
                    s,
                ))
            }
            Expr::LetIn { name, value, body } => {
                let (vv, vs) = self.go(value)?;
                let (bv, bs) = self.go(body)?;
                let let_in = |b: Expr| Expr::LetIn {
                    name: name.clone(),
                    value: Box::new(vv.clone()),
                    body: Box::new(b),
                };
                let safe = if bs == Expr::Bool(true) {
                    vs
                } else {
                    conj(vs, let_in(bs))
                };
                Some((let_in(bv), safe))
            }
            Expr::Quantifier {
                kind,
                var,
                domain,
                body,
            } => {
                let (dv, ds) = self.go(domain)?;
                let (bv, bs) = self.go(body)?;
                if bs != Expr::Bool(true) {
                    return None;
                }
                Some((
                    Expr::Quantifier {
                        kind: kind.clone(),
                        var: var.clone(),
                        domain: Box::new(dv),
                        body: Box::new(bv),
                    },
                    ds,
                ))
            }
            Expr::Call { func, args } => {
                let mut arg_vals = Vec::with_capacity(args.len());
                let mut safe = Expr::Bool(true);
                for a in args {
                    let (v, s) = self.go(a)?;
                    arg_vals.push(v);
                    safe = conj(safe, s);
                }
                let callee = match self.fns.get(func.as_str()) {
                    Some(f) if BuiltinFn::from_name(func).is_none() => *f,
                    _ => {
                        let call = Expr::Call {
                            func: func.clone(),
                            args: arg_vals,
                        };
                        return Some((call, safe));
                    }
                };
                if self.stack.contains(&callee.name.as_str()) || self.stack.len() >= MAX_DEPTH {
                    return None;
                }
                let (body, call_safe) = self.unfold_call(callee, &arg_vals)?;
                Some((body, conj(safe, call_safe)))
            }
            // Literals and variables need no unfolding. Forms the SMT encoding rejects anyway
            // (`if..fi`, `do..od`, `match`, records, lists) are left as-is.
            _ => Some((e.clone(), Expr::Bool(true))),
        }
    }

    /// Unfolds one call of `f` on already-unfolded `args`, in the order `eval.rs` checks it:
    /// requires, refined spec requires, body, ensures, refined spec ensures.
    fn unfold_call(&mut self, f: &'a FnDecl, args: &[Expr]) -> Option<(Expr, Expr)> {
        let map: BTreeMap<String, Expr> = f
            .params
            .iter()
            .map(|p| p.name.clone())
            .zip(args.iter().cloned())
            .collect();
        let spec = f.refines.as_deref().and_then(|s| self.specs.get(s).copied());
        let spec_map: BTreeMap<String, Expr> = spec
            .map(|s| {
                s.params
                    .iter()
                    .map(|p| p.name.clone())
                    .zip(args.iter().cloned())
                    .collect()
            })
            .unwrap_or_default();

        self.stack.push(f.name.as_str());
        let mut checks = Vec::new();
        if let Some(req) = &f.requires {
            checks.push(subst_expr(req, &map));
        }
        if let Some(sreq) = spec.and_then(|s| s.requires.as_ref()) {
            checks.push(subst_expr(sreq, &spec_map));
        }
        let mut safe = Expr::Bool(true);
        for c in checks {
            let (cv, cs) = self.go(&c)?;
            safe = conj(safe, conj(cs, cv));
        }
        let (body, body_safe) = self.go(&subst_expr(&f.body, &map))?;
        safe = conj(safe, body_safe);

        let mut post_checks = Vec::new();
        if let Some(ens) = &f.ensures {
            let mut m = map.clone();
            m.insert("result".into(), body.clone());
            post_checks.push(subst_expr(ens, &m));
        }
        if let Some(sens) = spec.and_then(|s| s.ensures.as_ref()) {
            let mut m = spec_map.clone();
            m.insert("result".into(), body.clone());
            post_checks.push(subst_expr(sens, &m));
        }
        for c in post_checks {
            let (cv, cs) = self.go(&c)?;
            safe = conj(safe, conj(cs, cv));
        }
        self.stack.pop();
        Some((body, safe))
    }
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
    if b == Expr::Bool(true) {
        return b;
    }
    bin(BinOp::Implies, a, b)
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
        let out = crate::expr_utils::format_expr_concise(&unfold_user_calls(&p, &vc).unwrap());
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
        let s = crate::expr_utils::format_expr_concise(&out);
        assert!(s.contains("b => "), "{s}");
    }
}
