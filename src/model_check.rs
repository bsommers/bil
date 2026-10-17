use crate::ast::*;
use crate::eval::{Interpreter, Value};
use crate::ontology::OntologyRegistry;
use crate::wp::format_expr_concise;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

#[derive(Debug, Clone)]
pub struct ModelCheckReport {
    pub system_name: String,
    pub states_explored: usize,
    pub transitions_fired: usize,
    pub max_depth: usize,
    pub max_branching_factor: usize,
    pub violations: Vec<ModelViolation>,
}

#[derive(Debug, Clone)]
pub enum ViolationKind {
    InvariantViolation(String),
    Deadlock,
    VariantNonDecreasing { prev: i64, next: i64, branch: usize },
    VariantNegative { val: i64 },
}

impl fmt::Display for ViolationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ViolationKind::InvariantViolation(name) => {
                write!(f, "Safety Invariant '{}' violated", name)
            }
            ViolationKind::Deadlock => {
                write!(f, "Deadlock (¬BB: no transition guard enabled in non-terminal state)")
            }
            ViolationKind::VariantNonDecreasing { prev, next, branch } => write!(
                f,
                "Termination Variant failed to decrease on transition #{}: {} -> {}",
                branch + 1,
                prev,
                next
            ),
            ViolationKind::VariantNegative { val } => {
                write!(f, "Termination Variant became negative: {}", val)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ModelViolation {
    pub kind: ViolationKind,
    pub state_str: String,
    pub trace: Vec<String>,
}

fn canonical_state_key(state: &BTreeMap<String, Value>) -> String {
    let parts: Vec<String> = state.iter().map(|(k, v)| format!("{}={}", k, v)).collect();
    parts.join("; ")
}

/// Exhaustively explores the nondeterministic state space of all `system` blocks (SPIN/Promela style)
pub fn model_check_program(
    program: &Program,
    ontology: &OntologyRegistry,
    max_states: usize,
) -> Result<Vec<ModelCheckReport>, String> {
    let mut reports = Vec::new();

    for item in &program.items {
        if let Item::System(sys) = item {
            reports.push(model_check_system(program, ontology, sys, max_states)?);
        }
    }

    Ok(reports)
}

fn model_check_system(
    program: &Program,
    ontology: &OntologyRegistry,
    sys: &SystemDecl,
    max_states: usize,
) -> Result<ModelCheckReport, String> {
    let mut interp = Interpreter::new(ontology.clone(), 1, false);
    interp
        .run_program(&Program {
            items: program
                .items
                .iter()
                .filter(|i| matches!(i, Item::TypeDecl(_) | Item::FnDecl(_) | Item::Spec(_)))
                .cloned()
                .collect(),
        })
        .map_err(|e| e.to_string())?;

    let mut init_state = BTreeMap::new();
    for st in &sys.states {
        let v = interp
            .eval_expr(&st.init, &init_state)
            .map_err(|e| e.to_string())?;
        init_state.insert(st.name.clone(), v);
    }

    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut queue: VecDeque<(BTreeMap<String, Value>, Vec<String>, usize)> = VecDeque::new();

    let init_key = canonical_state_key(&init_state);
    visited.insert(init_key.clone());
    queue.push_back((init_state, vec![format!("Init: {{ {} }}", init_key)], 0));

    let mut states_explored = 0usize;
    let mut transitions_fired = 0usize;
    let mut max_depth = 0usize;
    let mut max_branching_factor = 0usize;
    let mut violations = Vec::new();

    while let Some((state, trace, depth)) = queue.pop_front() {
        states_explored += 1;
        if depth > max_depth {
            max_depth = depth;
        }
        let state_str = format!("{{ {} }}", canonical_state_key(&state));

        // 1. Check all Safety Invariants in current reachable state
        for inv in &sys.invariants {
            let holds = interp
                .eval_expr(&inv.formula, &state)
                .map_err(|e| e.to_string())?;
            if holds != Value::Bool(true) {
                violations.push(ModelViolation {
                    kind: ViolationKind::InvariantViolation(inv.name.clone()),
                    state_str: state_str.clone(),
                    trace: trace.clone(),
                });
                return Ok(ModelCheckReport {
                    system_name: sys.name.clone(),
                    states_explored,
                    transitions_fired,
                    max_depth,
                    max_branching_factor,
                    violations,
                });
            }
        }

        // 2. Evaluate all guarded transitions (True Nondeterministic Interleaving)
        let mut enabled_branches = Vec::new();
        for (idx, tr) in sys.transitions.iter().enumerate() {
            let g = interp
                .eval_expr(&tr.guard, &state)
                .map_err(|e| e.to_string())?;
            if g == Value::Bool(true) {
                enabled_branches.push((idx, tr));
            }
        }

        if enabled_branches.len() > max_branching_factor {
            max_branching_factor = enabled_branches.len();
        }

        // 3. Deadlock detection: if no guard is enabled, check whether `terminal` holds
        if enabled_branches.is_empty() {
            let is_terminal = if let Some(term_expr) = &sys.terminal {
                interp
                    .eval_expr(term_expr, &state)
                    .map_err(|e| e.to_string())?
                    == Value::Bool(true)
            } else {
                false
            };
            if !is_terminal {
                violations.push(ModelViolation {
                    kind: ViolationKind::Deadlock,
                    state_str: state_str.clone(),
                    trace: trace.clone(),
                });
                return Ok(ModelCheckReport {
                    system_name: sys.name.clone(),
                    states_explored,
                    transitions_fired,
                    max_depth,
                    max_branching_factor,
                    violations,
                });
            }
            continue;
        }

        // Check current variant if present
        let curr_variant = if let Some(v_expr) = &sys.variant {
            if let Value::Int(v) = interp
                .eval_expr(v_expr, &state)
                .map_err(|e| e.to_string())?
            {
                if v < 0 {
                    violations.push(ModelViolation {
                        kind: ViolationKind::VariantNegative { val: v },
                        state_str: state_str.clone(),
                        trace: trace.clone(),
                    });
                    return Ok(ModelCheckReport {
                        system_name: sys.name.clone(),
                        states_explored,
                        transitions_fired,
                        max_depth,
                        max_branching_factor,
                        violations,
                    });
                }
                Some(v)
            } else {
                None
            }
        } else {
            None
        };

        // 4. Fire every enabled transition (exhaustively exploring all nondeterministic choices)
        for (br_idx, tr) in enabled_branches {
            transitions_fired += 1;
            let mut next_state = state.clone();
            let mut evaluated_updates = Vec::new();
            for (var, uexpr) in &tr.updates {
                let nv = interp
                    .eval_expr(uexpr, &state)
                    .map_err(|e| e.to_string())?;
                evaluated_updates.push((var.clone(), nv));
            }
            for (var, nv) in evaluated_updates {
                next_state.insert(var, nv);
            }

            let next_key = canonical_state_key(&next_state);
            let mut next_trace = trace.clone();
            next_trace.push(format!(
                "Step {} [Guard #{} {}] -> {{ {} }}",
                depth + 1,
                br_idx + 1,
                format_expr_concise(&tr.guard),
                next_key
            ));

            // Check variant strict decrease if variant is specified
            if let (Some(prev_v), Some(v_expr)) = (curr_variant, &sys.variant) {
                if let Value::Int(next_v) = interp
                    .eval_expr(v_expr, &next_state)
                    .map_err(|e| e.to_string())?
                {
                    if next_v >= prev_v {
                        violations.push(ModelViolation {
                            kind: ViolationKind::VariantNonDecreasing {
                                prev: prev_v,
                                next: next_v,
                                branch: br_idx,
                            },
                            state_str: format!("{{ {} }}", next_key),
                            trace: next_trace,
                        });
                        return Ok(ModelCheckReport {
                            system_name: sys.name.clone(),
                            states_explored,
                            transitions_fired,
                            max_depth,
                            max_branching_factor,
                            violations,
                        });
                    }
                }
            }

            if visited.len() < max_states && visited.insert(next_key) {
                queue.push_back((next_state, next_trace, depth + 1));
            }
        }
    }

    Ok(ModelCheckReport {
        system_name: sys.name.clone(),
        states_explored,
        transitions_fired,
        max_depth,
        max_branching_factor,
        violations,
    })
}
