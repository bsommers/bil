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

/// Lowers every system in `program`. Programs without `clock`/`deadline` are untouched.
pub fn lower_program(program: &mut Program) -> Result<(), ParseError> {
    let mut lowered = false;
    for item in &mut program.items {
        if let Item::System(sys) = item {
            lowered |= lower_system(sys)?;
        }
    }
    if lowered {
        // Generated expressions have no source span; `expr_spans` is documented to fall
        // back to item-level spans when empty.
        program.expr_spans.clear();
    }
    Ok(())
}

fn lower_system(sys: &mut SystemDecl) -> Result<bool, ParseError> {
    let clocks = std::mem::take(&mut sys.clocks);
    let deadlines = std::mem::take(&mut sys.deadlines);
    if clocks.is_empty() && deadlines.is_empty() {
        return Ok(false);
    }
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

    let mut seen = std::collections::BTreeSet::new();
    for d in deadlines {
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
        let n = (d.within_us + clock.period_us - 1) / clock.period_us;
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
    Ok(true)
}
