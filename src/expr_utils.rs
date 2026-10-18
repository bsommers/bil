//! Shared symbolic AST expression utilities (`free_vars`, capture-avoiding `subst_expr`,
//! `format_expr_concise`, and `extract_int_constants`) used across `wp`, `smt`, `model_check`, and `verus`.

use crate::ast::{Expr, GclBody, GuardedBranch, MatchArm, Pattern, QuantifierKind, UnaryOp};
use std::collections::{BTreeMap, BTreeSet};

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

/// Capture-avoiding simultaneous substitution `expr[var := replacement]` (Dijkstra's textual substitution).
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

/// Concise human-readable single-line formatting of an [`Expr`].
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

/// Extracts integer constants `c` and their immediate neighbors `c - 1, c, c + 1` from an expression
/// so bounded counterexample search automatically probes threshold boundaries.
pub fn extract_int_constants(expr: &Expr, out: &mut BTreeSet<i64>) {
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
