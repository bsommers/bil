//! Lowers `clock` / `deadline` members of a `system` into plain state, updates and invariants.
//!
//! One transition firing is one scan of the controller. For a deadline
//! `L => R within D` on a clock of period `P`, with `n = ceil(D / P)` and phase guard `G`:
//!
//! - `__run_<d>` is true after a scan that began with the latch pending: `(run || (G && L)) && !R`
//!   read in the pre-state. The phase guard is only read to *start* the timer, so a later phase
//!   change does not stop it and the bound of the phase that saw the latch keeps applying.
//! - `__t_<d>` counts the consecutive scans that began pending.
//! - `Deadline_<d>`: `__t_<d> >= n => R` (the response holds after the `n`-th scan).
//! - `Latch_<d>`: `__run_<d> => (L || R)` (the latch is not cleared before the response).

use crate::ast::*;
use crate::lexer::Span;
use crate::parser::ParseError;

fn var(name: &str) -> Expr {
    Expr::Var(name.to_string())
}

fn bin(op: BinOp, left: Expr, right: Expr) -> Expr {
    Expr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn not(e: Expr) -> Expr {
    Expr::Unary {
        op: UnaryOp::Not,
        expr: Box::new(e),
    }
}

fn err(message: String, span: Span) -> ParseError {
    ParseError { message, span }
}

fn count(e: &Expr) -> usize {
    let mut n = 0;
    e.walk_postorder(&mut |_| n += 1);
    n
}

/// Expression-node counts of each group of a system, in `expr_spans` order.
struct Counts {
    states: Vec<usize>,
    invariants: Vec<usize>,
    /// temporals + variant + terminal: never changed by lowering.
    middle: usize,
    transitions: Vec<usize>,
    deadlines: usize,
}

fn counts(sys: &SystemDecl) -> Counts {
    let mut middle = 0;
    Item::System(SystemDecl {
        states: vec![],
        invariants: vec![],
        transitions: vec![],
        deadlines: vec![],
        clocks: vec![],
        ..sys.clone()
    })
    .for_each_expr_postorder(&mut |_| middle += 1);
    let mut deadlines = 0;
    for d in &sys.deadlines {
        deadlines += count(&d.latch) + count(&d.response) + d.phase.as_ref().map_or(0, count);
    }
    Counts {
        states: sys.states.iter().map(|s| count(&s.init)).collect(),
        invariants: sys.invariants.iter().map(|i| count(&i.formula)).collect(),
        middle,
        transitions: sys
            .transitions
            .iter()
            .map(|t| count(&t.guard) + t.updates.iter().map(|(_, e)| count(e)).sum::<usize>())
            .collect(),
        deadlines,
    }
}

/// Lowers every system in `program`, keeping `expr_spans` aligned with the expression walk:
/// generated nodes take the span of their system. Programs without `clock`/`deadline` are
/// untouched.
pub fn lower_program(program: &mut Program) -> Result<(), ParseError> {
    let spanned = !program.expr_spans.is_empty();
    let old = std::mem::take(&mut program.expr_spans);
    let mut out = Vec::with_capacity(old.len());
    let mut at = 0;
    for item in &mut program.items {
        let mut n = 0;
        item.for_each_expr_postorder(&mut |_| n += 1);
        let slice = if spanned { &old[at..at + n] } else { &[][..] };
        at += n;
        let Item::System(sys) = item else {
            out.extend_from_slice(slice);
            continue;
        };
        if sys.clocks.is_empty() && sys.deadlines.is_empty() {
            out.extend_from_slice(slice);
            continue;
        }
        let before = counts(sys);
        lower_system(sys)?;
        if spanned {
            out.extend(rebuild_spans(slice, &before, &counts(sys), sys.span));
        }
    }
    if spanned {
        program.expr_spans = out;
    }
    Ok(())
}

/// The span slice of a lowered system: original nodes keep their spans, nodes added at the end
/// of a state, invariant or transition take `fallback`, and the consumed deadlines' spans go.
fn rebuild_spans(old: &[Span], before: &Counts, after: &Counts, fallback: Span) -> Vec<Span> {
    let mut out = Vec::new();
    let mut at = 0;
    let list = |old_counts: &[usize], new_counts: &[usize], out: &mut Vec<Span>, at: &mut usize| {
        for (i, &new) in new_counts.iter().enumerate() {
            let kept = old_counts.get(i).copied().unwrap_or(0);
            out.extend_from_slice(&old[*at..*at + kept]);
            *at += kept;
            out.extend(std::iter::repeat_n(fallback, new - kept));
        }
    };
    list(&before.states, &after.states, &mut out, &mut at);
    list(&before.invariants, &after.invariants, &mut out, &mut at);
    out.extend_from_slice(&old[at..at + before.middle]);
    at += before.middle;
    list(&before.transitions, &after.transitions, &mut out, &mut at);
    debug_assert_eq!(at + before.deadlines, old.len());
    out
}

fn lower_system(sys: &mut SystemDecl) -> Result<(), ParseError> {
    let clocks = std::mem::take(&mut sys.clocks);
    let deadlines = std::mem::take(&mut sys.deadlines);
    if clocks.len() > 1 {
        return Err(err(
            format!("system `{}` declares more than one `clock`", sys.name),
            clocks[1].span,
        ));
    }
    let Some(clock) = clocks.first() else {
        return Err(err(
            format!("`deadline` in system `{}` needs a `clock` declaring the scan period", sys.name),
            deadlines[0].span,
        ));
    };

    let at = deadlines[0].span;
    for st in &sys.states {
        if st.name.starts_with("__") {
            return Err(err(
                format!("state `{}` uses the reserved `__` prefix (timed guards generate `__run_*`/`__t_*`)", st.name),
                at,
            ));
        }
    }
    for tr in &sys.transitions {
        if let Some((name, _)) = tr.updates.iter().find(|(n, _)| n.starts_with("__")) {
            return Err(err(format!("update of `{name}` uses the reserved `__` prefix"), at));
        }
    }
    let mut seen = std::collections::BTreeSet::new();
    for d in deadlines {
        for generated in [format!("Deadline_{}", d.name), format!("Latch_{}", d.name)] {
            if sys.invariants.iter().any(|i| i.name == generated) {
                return Err(err(
                    format!("invariant `{generated}` collides with the one generated for deadline `{}`", d.name),
                    d.span,
                ));
            }
        }
        if !seen.insert(d.name.clone()) {
            return Err(err(format!("duplicate deadline `{}`", d.name), d.span));
        }
        if d.within_us < clock.period_us {
            return Err(err(
                format!(
                    "deadline `{}` ({} us) is shorter than the scan period of clock `{}` ({} us)",
                    d.name, d.within_us, clock.name, clock.period_us
                ),
                d.span,
            ));
        }
        let n = d.within_us / clock.period_us + i64::from(d.within_us % clock.period_us != 0);
        let (run, t) = (format!("__run_{}", d.name), format!("__t_{}", d.name));
        let started = bin(
            BinOp::And,
            d.phase.clone().unwrap_or(Expr::Bool(true)),
            d.latch.clone(),
        );
        let pending = bin(
            BinOp::And,
            bin(BinOp::Or, var(&run), started),
            not(d.response.clone()),
        );
        let counter = Expr::IfFi {
            branches: vec![
                GuardedBranch {
                    guard: pending.clone(),
                    body: GclBody::Expr(bin(BinOp::Add, var(&t), Expr::Int(1))),
                },
                GuardedBranch {
                    guard: not(pending.clone()),
                    body: GclBody::Expr(Expr::Int(0)),
                },
            ],
        };
        for tr in &mut sys.transitions {
            tr.updates.push((run.clone(), pending.clone()));
            tr.updates.push((t.clone(), counter.clone()));
        }
        sys.states.push(StateVarDecl {
            name: run.clone(),
            ty: TypeExpr::Named("Bool".into()),
            init: Expr::Bool(false),
        });
        sys.states.push(StateVarDecl {
            name: t.clone(),
            ty: TypeExpr::Named("Int".into()),
            init: Expr::Int(0),
        });
        sys.invariants.push(NamedInvariant {
            name: format!("Deadline_{}", d.name),
            formula: bin(
                BinOp::Implies,
                bin(BinOp::Ge, var(&t), Expr::Int(n)),
                d.response.clone(),
            ),
        });
        sys.invariants.push(NamedInvariant {
            name: format!("Latch_{}", d.name),
            formula: bin(
                BinOp::Implies,
                var(&run),
                bin(BinOp::Or, d.latch.clone(), d.response.clone()),
            ),
        });
    }
    Ok(())
}
