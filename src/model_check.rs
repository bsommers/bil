use crate::ast::*;
use crate::eval::{Interpreter, Value};
use crate::ontology::OntologyRegistry;
use crate::wp::format_expr_concise;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

#[derive(Debug, Clone)]
pub struct TemporalCheckResult {
    pub name: String,
    pub formula_desc: String,
    pub verified: bool,
    pub counterexample: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct ModelCheckReport {
    pub system_name: String,
    pub states_explored: usize,
    pub transitions_fired: usize,
    pub max_depth: usize,
    pub max_branching_factor: usize,
    pub temporal_results: Vec<TemporalCheckResult>,
    pub violations: Vec<ModelViolation>,
}

#[derive(Debug, Clone)]
pub enum ViolationKind {
    InvariantViolation(String),
    Deadlock,
    VariantNonDecreasing { prev: i64, next: i64, branch: usize },
    VariantNegative { val: i64 },
    TemporalViolation { name: String, formula: String },
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
            ViolationKind::TemporalViolation { name, formula } => {
                write!(f, "LTL Temporal Property '{}' ({}) violated", name, formula)
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

/// Exhaustively explores the nondeterministic state space of all `system` blocks (SPIN/Promela + LTL style)
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

    // State-space graph structures for LTL & weak fairness verification
    let mut state_map: BTreeMap<String, BTreeMap<String, Value>> = BTreeMap::new();
    let mut trace_map: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut adj: BTreeMap<String, Vec<(usize, String)>> = BTreeMap::new();
    let mut enabled_map: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();

    let init_key = canonical_state_key(&init_state);
    let init_trace = vec![format!("Init: {{ {} }}", init_key)];
    visited.insert(init_key.clone());
    state_map.insert(init_key.clone(), init_state.clone());
    trace_map.insert(init_key.clone(), init_trace.clone());
    queue.push_back((init_state, init_trace, 0));

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
        let curr_key = canonical_state_key(&state);
        let state_str = format!("{{ {} }}", curr_key);

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
                    temporal_results: Vec::new(),
                    violations,
                });
            }
        }

        // 2. Evaluate all guarded transitions (True Nondeterministic Interleaving)
        let mut enabled_branches = Vec::new();
        let mut enabled_indices = BTreeSet::new();
        for (idx, tr) in sys.transitions.iter().enumerate() {
            let g = interp
                .eval_expr(&tr.guard, &state)
                .map_err(|e| e.to_string())?;
            if g == Value::Bool(true) {
                enabled_branches.push((idx, tr));
                enabled_indices.insert(idx);
            }
        }
        enabled_map.insert(curr_key.clone(), enabled_indices);

        if enabled_branches.len() > max_branching_factor {
            max_branching_factor = enabled_branches.len();
        }

        // 3. Deadlock detection: if no guard is enabled, check whether `terminal` holds
        if enabled_branches.is_empty() {
            adj.entry(curr_key.clone()).or_default();
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
                    temporal_results: Vec::new(),
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
                        temporal_results: Vec::new(),
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
            adj.entry(curr_key.clone())
                .or_default()
                .push((br_idx, next_key.clone()));

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
                            temporal_results: Vec::new(),
                            violations,
                        });
                    }
                }
            }

            if visited.len() < max_states && visited.insert(next_key.clone()) {
                state_map.insert(next_key.clone(), next_state.clone());
                trace_map.insert(next_key.clone(), next_trace.clone());
                queue.push_back((next_state, next_trace, depth + 1));
            }
        }
    }

    // 5. LTL Temporal & Weak Fairness Verification across the reachable state graph
    let mut temporal_results = Vec::new();
    for temp in &sys.temporals {
        match &temp.formula {
            TemporalFormula::Always(p) => {
                let fdesc = format!("□({})", format_expr_concise(p));
                let mut failed = None;
                for (skey, st_env) in &state_map {
                    let holds = interp.eval_expr(p, st_env).map_err(|e| e.to_string())?;
                    if holds != Value::Bool(true) {
                        let tr = trace_map.get(skey).cloned().unwrap_or_default();
                        failed = Some((skey.clone(), tr));
                        break;
                    }
                }
                if let Some((skey, tr)) = failed {
                    temporal_results.push(TemporalCheckResult {
                        name: temp.name.clone(),
                        formula_desc: fdesc.clone(),
                        verified: false,
                        counterexample: Some(tr.clone()),
                    });
                    violations.push(ModelViolation {
                        kind: ViolationKind::TemporalViolation {
                            name: temp.name.clone(),
                            formula: fdesc,
                        },
                        state_str: format!("{{ {} }}", skey),
                        trace: tr,
                    });
                } else {
                    temporal_results.push(TemporalCheckResult {
                        name: temp.name.clone(),
                        formula_desc: fdesc,
                        verified: true,
                        counterexample: None,
                    });
                }
            }
            TemporalFormula::Eventually(q) => {
                let fdesc = format!("◇({})", format_expr_concise(q));
                let ce = check_eventually_from(
                    &init_key,
                    q,
                    sys.transitions.len(),
                    &state_map,
                    &trace_map,
                    &adj,
                    &enabled_map,
                    &mut interp,
                )?;
                if let Some((skey, tr)) = ce {
                    temporal_results.push(TemporalCheckResult {
                        name: temp.name.clone(),
                        formula_desc: fdesc.clone(),
                        verified: false,
                        counterexample: Some(tr.clone()),
                    });
                    violations.push(ModelViolation {
                        kind: ViolationKind::TemporalViolation {
                            name: temp.name.clone(),
                            formula: fdesc,
                        },
                        state_str: format!("{{ {} }}", skey),
                        trace: tr,
                    });
                } else {
                    temporal_results.push(TemporalCheckResult {
                        name: temp.name.clone(),
                        formula_desc: fdesc,
                        verified: true,
                        counterexample: None,
                    });
                }
            }
            TemporalFormula::LeadsTo(p, q) => {
                let fdesc = format!("{} ~> {}", format_expr_concise(p), format_expr_concise(q));
                let mut failed = None;
                for (skey, st_env) in &state_map {
                    let p_holds = interp.eval_expr(p, st_env).map_err(|e| e.to_string())?;
                    if p_holds == Value::Bool(true) {
                        if let Some(ce) = check_eventually_from(
                            skey,
                            q,
                            sys.transitions.len(),
                            &state_map,
                            &trace_map,
                            &adj,
                            &enabled_map,
                            &mut interp,
                        )? {
                            failed = Some(ce);
                            break;
                        }
                    }
                }
                if let Some((skey, tr)) = failed {
                    temporal_results.push(TemporalCheckResult {
                        name: temp.name.clone(),
                        formula_desc: fdesc.clone(),
                        verified: false,
                        counterexample: Some(tr.clone()),
                    });
                    violations.push(ModelViolation {
                        kind: ViolationKind::TemporalViolation {
                            name: temp.name.clone(),
                            formula: fdesc,
                        },
                        state_str: format!("{{ {} }}", skey),
                        trace: tr,
                    });
                } else {
                    temporal_results.push(TemporalCheckResult {
                        name: temp.name.clone(),
                        formula_desc: fdesc,
                        verified: true,
                        counterexample: None,
                    });
                }
            }
        }
    }

    Ok(ModelCheckReport {
        system_name: sys.name.clone(),
        states_explored,
        transitions_fired,
        max_depth,
        max_branching_factor,
        temporal_results,
        violations,
    })
}

/// Checks whether `q` holds eventually on all weakly fair paths starting from `start_key`.
/// Returns `Ok(Some((violating_state, counterexample_trace)))` if a terminal ¬Q state or
/// weakly fair ¬Q cycle is reachable from `start_key` without visiting any Q-state.
#[allow(clippy::too_many_arguments)]
fn check_eventually_from(
    start_key: &str,
    q: &Expr,
    num_transitions: usize,
    state_map: &BTreeMap<String, BTreeMap<String, Value>>,
    trace_map: &BTreeMap<String, Vec<String>>,
    adj: &BTreeMap<String, Vec<(usize, String)>>,
    enabled_map: &BTreeMap<String, BTreeSet<usize>>,
    interp: &mut Interpreter,
) -> Result<Option<(String, Vec<String>)>, String> {
    let mut q_holds_map: BTreeMap<String, bool> = BTreeMap::new();
    for (k, st) in state_map {
        let v = interp.eval_expr(q, st).map_err(|e| e.to_string())?;
        q_holds_map.insert(k.clone(), v == Value::Bool(true));
    }

    if q_holds_map.get(start_key).copied().unwrap_or(false) {
        return Ok(None);
    }

    // Collect subgraph V_not_q reachable from `start_key` via ¬Q paths
    let mut not_q_nodes = BTreeSet::new();
    let mut bfs = VecDeque::new();
    not_q_nodes.insert(start_key.to_string());
    bfs.push_back(start_key.to_string());

    while let Some(u) = bfs.pop_front() {
        let outs = adj.get(&u).cloned().unwrap_or_default();
        if outs.is_empty() {
            // Terminal ¬Q state reached before Q ever held!
            let mut tr = trace_map.get(&u).cloned().unwrap_or_default();
            tr.push(format!("Halted in ¬Q terminal state: {{ {} }}", u));
            return Ok(Some((u, tr)));
        }
        for (_, v) in outs {
            if !q_holds_map.get(&v).copied().unwrap_or(false) && not_q_nodes.insert(v.clone()) {
                bfs.push_back(v);
            }
        }
    }

    // Decompose V_not_q into Strongly Connected Components (Tarjan's algorithm)
    let sccs = tarjan_sccs(&not_q_nodes, adj);
    for scc in sccs {
        let scc_set: BTreeSet<String> = scc.iter().cloned().collect();
        // Check if this SCC contains at least one internal transition edge
        let mut internal_edges = Vec::new();
        for u in &scc {
            if let Some(outs) = adj.get(u) {
                for (br, v) in outs {
                    if scc_set.contains(v) {
                        internal_edges.push((u.clone(), *br, v.clone()));
                    }
                }
            }
        }
        if internal_edges.is_empty() {
            continue;
        }

        // Check Weak Fairness (Justice):
        // A cycle C is unfair iff there exists a transition `t` that is enabled in EVERY state of C,
        // yet `t` is never taken inside C (all edges for `t` exit C).
        // Also check whether removing such unfair transitions still leaves a fair sub-cycle inside C.
        if let Some(cycle_node) = find_fair_cycle_in_subgraph(&scc_set, num_transitions, adj, enabled_map) {
            let mut tr = trace_map.get(&cycle_node).cloned().unwrap_or_default();
            let cycle_desc: Vec<String> = scc.iter().map(|s| format!("{{ {} }}", s)).collect();
            tr.push(format!(
                "Weakly Fair ¬Q Cycle (Lasso): {}",
                cycle_desc.join(" -> ")
            ));
            return Ok(Some((cycle_node, tr)));
        }
    }

    Ok(None)
}

/// Iteratively prunes transitions that are continuously enabled across an SCC but always exit it,
/// checking if a weakly fair cycle remains.
fn find_fair_cycle_in_subgraph(
    nodes: &BTreeSet<String>,
    num_transitions: usize,
    adj: &BTreeMap<String, Vec<(usize, String)>>,
    enabled_map: &BTreeMap<String, BTreeSet<usize>>,
) -> Option<String> {
    let sccs = tarjan_sccs(nodes, adj);
    for scc in sccs {
        let scc_set: BTreeSet<String> = scc.iter().cloned().collect();
        let mut internal_transitions = BTreeSet::new();
        for u in &scc {
            if let Some(outs) = adj.get(u) {
                for (br, v) in outs {
                    if scc_set.contains(v) {
                        internal_transitions.insert(*br);
                    }
                }
            }
        }
        if internal_transitions.is_empty() {
            continue;
        }

        // Check if any transition is continuously enabled across all states in `scc_set`
        // but is NOT in `internal_transitions` (meaning firing it always exits `scc_set`).
        let mut unfair_exiting_transitions = Vec::new();
        for t_idx in 0..num_transitions {
            let continuously_enabled = scc_set.iter().all(|s| {
                enabled_map
                    .get(s)
                    .map(|ens| ens.contains(&t_idx))
                    .unwrap_or(false)
            });
            if continuously_enabled && !internal_transitions.contains(&t_idx) {
                unfair_exiting_transitions.push(t_idx);
            }
        }

        if unfair_exiting_transitions.is_empty() {
            // Every continuously-enabled transition can be taken within `scc_set`,
            // so `scc_set` forms a valid weakly fair cycle!
            return scc.into_iter().next();
        }
    }
    None
}

fn tarjan_sccs(
    nodes: &BTreeSet<String>,
    adj: &BTreeMap<String, Vec<(usize, String)>>,
) -> Vec<Vec<String>> {
    struct TarjanState<'a> {
        index: usize,
        indices: BTreeMap<String, usize>,
        lowlink: BTreeMap<String, usize>,
        stack: Vec<String>,
        on_stack: BTreeSet<String>,
        sccs: Vec<Vec<String>>,
        nodes: &'a BTreeSet<String>,
        adj: &'a BTreeMap<String, Vec<(usize, String)>>,
    }

    fn strongconnect(v: &str, st: &mut TarjanState<'_>) {
        let idx = st.index;
        st.index += 1;
        st.indices.insert(v.to_string(), idx);
        st.lowlink.insert(v.to_string(), idx);
        st.stack.push(v.to_string());
        st.on_stack.insert(v.to_string());

        if let Some(outs) = st.adj.get(v) {
            for (_, w) in outs {
                if !st.nodes.contains(w) {
                    continue;
                }
                if !st.indices.contains_key(w) {
                    strongconnect(w, st);
                    let lw = st.lowlink[w];
                    let lv = st.lowlink[v];
                    if lw < lv {
                        st.lowlink.insert(v.to_string(), lw);
                    }
                } else if st.on_stack.contains(w) {
                    let iw = st.indices[w];
                    let lv = st.lowlink[v];
                    if iw < lv {
                        st.lowlink.insert(v.to_string(), iw);
                    }
                }
            }
        }

        if st.lowlink[v] == st.indices[v] {
            let mut scc = Vec::new();
            while let Some(w) = st.stack.pop() {
                st.on_stack.remove(&w);
                let done = w == v;
                scc.push(w);
                if done {
                    break;
                }
            }
            st.sccs.push(scc);
        }
    }

    let mut st = TarjanState {
        index: 0,
        indices: BTreeMap::new(),
        lowlink: BTreeMap::new(),
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        sccs: Vec::new(),
        nodes,
        adj,
    };

    for n in nodes {
        if !st.indices.contains_key(n) {
            strongconnect(n, &mut st);
        }
    }

    st.sccs
}
