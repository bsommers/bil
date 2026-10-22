use crate::ast::*;
use crate::eval::{Interpreter, Value};
use crate::expr_utils::{format_expr_concise, subst_expr};
use crate::ontology::OntologyRegistry;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

#[derive(Debug, Clone, Serialize)]
pub struct TemporalCheckResult {
    pub name: String,
    pub formula_desc: String,
    pub verified: bool,
    pub counterexample: Option<Vec<String>>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ModelCheckReport {
    pub system_name: String,
    pub states_explored: usize,
    pub transitions_fired: usize,
    pub max_depth: usize,
    pub max_branching_factor: usize,
    pub complete: bool,
    pub truncated_at: Option<usize>,
    pub temporal_results: Vec<TemporalCheckResult>,
    pub violations: Vec<ModelViolation>,
}

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
pub struct ModelViolation {
    pub kind: ViolationKind,
    pub state_str: String,
    pub trace: Vec<String>,
}

fn display_state_key(state: &BTreeMap<String, Value>) -> String {
    let parts: Vec<String> = state.iter().map(|(k, v)| format!("{}={}", k, v)).collect();
    parts.join("; ")
}

fn encode_value_canonical(v: &Value, out: &mut String) {
    match v {
        Value::Int(n) => out.push_str(&format!("I:{};", n)),
        Value::Float(f) => out.push_str(&format!("F:{};", f.to_bits())),
        Value::Bool(b) => out.push_str(if *b { "B:1;" } else { "B:0;" }),
        Value::Str(s) => out.push_str(&format!("S:{}:{};", s.len(), s)),
        Value::Unit => out.push_str("U;"),
        Value::List(items) => {
            out.push_str(&format!("L:{}:[", items.len()));
            for item in items.iter() {
                encode_value_canonical(item, out);
            }
            out.push_str("];");
        }
        Value::ConceptInstance { concept, fields } => {
            out.push_str(&format!("R:{}:{}:{}:{{", concept.len(), concept, fields.len()));
            for (k, fv) in fields {
                out.push_str(&format!("{}:{}:", k.len(), k));
                encode_value_canonical(fv, out);
            }
            out.push_str("};");
        }
        Value::AdtVariant { variant, fields } => {
            out.push_str(&format!(
                "V:{}:{}:{}:(",
                variant.len(),
                variant,
                fields.len()
            ));
            for pv in fields {
                encode_value_canonical(pv, out);
            }
            out.push_str(");");
        }
        Value::PartialCall { func, args } => {
            out.push_str(&format!("P:{}:{}:{}:(", func.len(), func, args.len()));
            for arg in args {
                match arg {
                    Some(av) => {
                        out.push_str("1:");
                        encode_value_canonical(av, out);
                    }
                    None => out.push_str("0;"),
                }
            }
            out.push_str(");");
        }
    }
}

/// Collision-free length-prefixed canonical key for state table interning.
fn collision_free_state_key(state: &BTreeMap<String, Value>) -> String {
    let mut out = format!("N:{};", state.len());
    for (k, v) in state {
        out.push_str(&format!("K:{}:{}:", k.len(), k));
        encode_value_canonical(v, &mut out);
    }
    out
}

/// Reconstructs a human-readable execution trace from the root state (`0`) to `state_id`
/// using parent pointers in $O(\text{depth})$ time.
fn reconstruct_trace(
    state_id: usize,
    state_display: &[String],
    parent: &[Option<(usize, usize, usize)>],
    transitions: &[GuardedTransition],
) -> Vec<String> {
    let mut steps = Vec::new();
    let mut curr = state_id;
    while let Some((p_id, br_idx, depth)) = parent[curr] {
        let guard_str = format_expr_concise(&transitions[br_idx].guard);
        steps.push(format!(
            "Step {} [Guard #{} {}] -> {{ {} }}",
            depth,
            br_idx + 1,
            guard_str,
            state_display[curr]
        ));
        curr = p_id;
    }
    steps.push(format!("Init: {{ {} }}", state_display[curr]));
    steps.reverse();
    steps
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

    // Interned state-space graph structures (state ID = usize in 0..states.len())
    let mut states: Vec<BTreeMap<String, Value>> = Vec::new();
    let mut state_display: Vec<String> = Vec::new();
    let mut state_to_id: BTreeMap<String, usize> = BTreeMap::new();
    let mut parent: Vec<Option<(usize, usize, usize)>> = Vec::new();
    let mut adj: Vec<Vec<(usize, usize)>> = Vec::new();
    let mut enabled_map: Vec<BTreeSet<usize>> = Vec::new();
    let mut truncated_frontier: BTreeSet<usize> = BTreeSet::new();
    let mut queue: VecDeque<(usize, usize)> = VecDeque::new();

    let init_id_key = collision_free_state_key(&init_state);
    let init_disp = display_state_key(&init_state);
    states.push(init_state);
    state_display.push(init_disp);
    state_to_id.insert(init_id_key, 0);
    parent.push(None);
    adj.push(Vec::new());
    enabled_map.push(BTreeSet::new());
    if max_states > 0 {
        queue.push_back((0, 0));
    }

    let mut states_explored = 0usize;
    let mut transitions_fired = 0usize;
    let mut max_depth = 0usize;
    let mut max_branching_factor = 0usize;
    let mut complete = max_states > 0;
    let mut truncated_at = if max_states == 0 { Some(0) } else { None };
    let mut violations = Vec::new();

    while let Some((curr_id, depth)) = queue.pop_front() {
        states_explored += 1;
        if depth > max_depth {
            max_depth = depth;
        }
        let state = states[curr_id].clone();
        let curr_disp = state_display[curr_id].clone();
        let state_str = format!("{{ {} }}", curr_disp);

        // 1. Check all Safety Invariants in current reachable state
        for inv in &sys.invariants {
            let holds = interp
                .eval_expr(&inv.formula, &state)
                .map_err(|e| e.to_string())?;
            if holds != Value::Bool(true) {
                let trace = reconstruct_trace(curr_id, &state_display, &parent, &sys.transitions);
                violations.push(ModelViolation {
                    kind: ViolationKind::InvariantViolation(inv.name.clone()),
                    state_str,
                    trace,
                });
                return Ok(ModelCheckReport {
                    system_name: sys.name.clone(),
                    states_explored,
                    transitions_fired,
                    max_depth,
                    max_branching_factor,
                    complete,
                    truncated_at,
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
        enabled_map[curr_id] = enabled_indices;

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
                let trace = reconstruct_trace(curr_id, &state_display, &parent, &sys.transitions);
                violations.push(ModelViolation {
                    kind: ViolationKind::Deadlock,
                    state_str,
                    trace,
                });
                return Ok(ModelCheckReport {
                    system_name: sys.name.clone(),
                    states_explored,
                    transitions_fired,
                    max_depth,
                    max_branching_factor,
                    complete,
                    truncated_at,
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
                    let trace =
                        reconstruct_trace(curr_id, &state_display, &parent, &sys.transitions);
                    violations.push(ModelViolation {
                        kind: ViolationKind::VariantNegative { val: v },
                        state_str,
                        trace,
                    });
                    return Ok(ModelCheckReport {
                        system_name: sys.name.clone(),
                        states_explored,
                        transitions_fired,
                        max_depth,
                        max_branching_factor,
                        complete,
                        truncated_at,
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

            let next_disp = display_state_key(&next_state);

            // Check variant strict decrease if variant is specified
            if let (Some(prev_v), Some(v_expr)) = (curr_variant, &sys.variant) {
                if let Value::Int(next_v) = interp
                    .eval_expr(v_expr, &next_state)
                    .map_err(|e| e.to_string())?
                {
                    if next_v >= prev_v {
                        let mut next_trace =
                            reconstruct_trace(curr_id, &state_display, &parent, &sys.transitions);
                        next_trace.push(format!(
                            "Step {} [Guard #{} {}] -> {{ {} }}",
                            depth + 1,
                            br_idx + 1,
                            format_expr_concise(&tr.guard),
                            next_disp
                        ));
                        violations.push(ModelViolation {
                            kind: ViolationKind::VariantNonDecreasing {
                                prev: prev_v,
                                next: next_v,
                                branch: br_idx,
                            },
                            state_str: format!("{{ {} }}", next_disp),
                            trace: next_trace,
                        });
                        return Ok(ModelCheckReport {
                            system_name: sys.name.clone(),
                            states_explored,
                            transitions_fired,
                            max_depth,
                            max_branching_factor,
                            complete,
                            truncated_at,
                            temporal_results: Vec::new(),
                            violations,
                        });
                    }
                }
            }

            let next_id_key = collision_free_state_key(&next_state);
            if let Some(&existing_id) = state_to_id.get(&next_id_key) {
                adj[curr_id].push((br_idx, existing_id));
            } else if states.len() < max_states {
                let new_id = states.len();
                states.push(next_state);
                state_display.push(next_disp);
                state_to_id.insert(next_id_key, new_id);
                parent.push(Some((curr_id, br_idx, depth + 1)));
                adj.push(Vec::new());
                enabled_map.push(BTreeSet::new());
                adj[curr_id].push((br_idx, new_id));
                queue.push_back((new_id, depth + 1));
            } else {
                complete = false;
                if truncated_at.is_none() {
                    truncated_at = Some(max_states);
                }
                truncated_frontier.insert(curr_id);
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
                for (sid, st_env) in states.iter().enumerate() {
                    let holds = interp.eval_expr(p, st_env).map_err(|e| e.to_string())?;
                    if holds != Value::Bool(true) {
                        let tr = reconstruct_trace(sid, &state_display, &parent, &sys.transitions);
                        failed = Some((state_display[sid].clone(), tr));
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
                let mut q_holds = Vec::with_capacity(states.len());
                for st in &states {
                    let v = interp.eval_expr(q, st).map_err(|e| e.to_string())?;
                    q_holds.push(v == Value::Bool(true));
                }
                let ce = check_eventually_from(
                    0,
                    &q_holds,
                    &sys.transitions,
                    &state_display,
                    &parent,
                    &adj,
                    &enabled_map,
                    &truncated_frontier,
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
                let mut q_holds = Vec::with_capacity(states.len());
                for st in &states {
                    let v = interp.eval_expr(q, st).map_err(|e| e.to_string())?;
                    q_holds.push(v == Value::Bool(true));
                }
                let mut failed = None;
                for (sid, st_env) in states.iter().enumerate() {
                    let p_holds = interp.eval_expr(p, st_env).map_err(|e| e.to_string())?;
                    if p_holds == Value::Bool(true) {
                        if let Some(ce) = check_eventually_from(
                            sid,
                            &q_holds,
                            &sys.transitions,
                            &state_display,
                            &parent,
                            &adj,
                            &enabled_map,
                            &truncated_frontier,
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
        complete,
        truncated_at,
        temporal_results,
        violations,
    })
}

/// Checks whether `q` holds eventually on all weakly fair paths starting from `start_id`.
/// Returns `Ok(Some((violating_state, counterexample_trace)))` if a genuine terminal ¬Q state or
/// weakly fair ¬Q cycle is reachable from `start_id` without visiting any Q-state.
#[allow(clippy::too_many_arguments)]
fn check_eventually_from(
    start_id: usize,
    q_holds: &[bool],
    transitions: &[GuardedTransition],
    state_display: &[String],
    parent: &[Option<(usize, usize, usize)>],
    adj: &[Vec<(usize, usize)>],
    enabled_map: &[BTreeSet<usize>],
    truncated_frontier: &BTreeSet<usize>,
) -> Result<Option<(String, Vec<String>)>, String> {
    if q_holds.get(start_id).copied().unwrap_or(false) {
        return Ok(None);
    }

    // Collect subgraph V_not_q reachable from `start_id` via ¬Q paths
    let mut not_q_nodes = BTreeSet::new();
    let mut bfs = VecDeque::new();
    not_q_nodes.insert(start_id);
    bfs.push_back(start_id);

    while let Some(u) = bfs.pop_front() {
        let outs = &adj[u];
        if outs.is_empty() {
            // Only report a terminal ¬Q violation if `u` is a genuine terminal state,
            // NOT a frontier state whose outgoing transitions were truncated by `max_states`.
            if !truncated_frontier.contains(&u) {
                let mut tr = reconstruct_trace(u, state_display, parent, transitions);
                tr.push(format!(
                    "Halted in ¬Q terminal state: {{ {} }}",
                    state_display[u]
                ));
                return Ok(Some((state_display[u].clone(), tr)));
            }
            continue;
        }
        for &(_, v) in outs {
            if !q_holds[v] && not_q_nodes.insert(v) {
                bfs.push_back(v);
            }
        }
    }

    let num_transitions = transitions.len();
    // Decompose V_not_q into Strongly Connected Components (single Tarjan pass)
    let sccs = tarjan_sccs(&not_q_nodes, adj);
    for scc in sccs {
        let scc_set: BTreeSet<usize> = scc.iter().copied().collect();
        let mut internal_transitions = BTreeSet::new();
        for &u in &scc {
            for &(br, v) in &adj[u] {
                if scc_set.contains(&v) {
                    internal_transitions.insert(br);
                }
            }
        }
        if internal_transitions.is_empty() {
            continue;
        }

        // Check Weak Fairness (Justice): whether any transition is continuously enabled across
        // all states in `scc_set` without appearing in `internal_transitions`.
        let has_unfair_exit = (0..num_transitions).any(|t_idx| {
            !internal_transitions.contains(&t_idx)
                && scc_set.iter().all(|&s| enabled_map[s].contains(&t_idx))
        });

        if !has_unfair_exit {
            if let Some(&cycle_node) = scc.first() {
                let mut tr = reconstruct_trace(cycle_node, state_display, parent, transitions);
                let cycle_desc: Vec<String> = scc
                    .iter()
                    .map(|&s| format!("{{ {} }}", state_display[s]))
                    .collect();
                tr.push(format!(
                    "Weakly Fair ¬Q Cycle (Lasso): {}",
                    cycle_desc.join(" -> ")
                ));
                return Ok(Some((state_display[cycle_node].clone(), tr)));
            }
        }
    }

    Ok(None)
}

fn tarjan_sccs(nodes: &BTreeSet<usize>, adj: &[Vec<(usize, usize)>]) -> Vec<Vec<usize>> {
    struct TarjanState<'a> {
        index: usize,
        indices: BTreeMap<usize, usize>,
        lowlink: BTreeMap<usize, usize>,
        stack: Vec<usize>,
        on_stack: BTreeSet<usize>,
        sccs: Vec<Vec<usize>>,
        nodes: &'a BTreeSet<usize>,
        adj: &'a [Vec<(usize, usize)>],
    }

    fn strongconnect(v: usize, st: &mut TarjanState<'_>) {
        let idx = st.index;
        st.index += 1;
        st.indices.insert(v, idx);
        st.lowlink.insert(v, idx);
        st.stack.push(v);
        st.on_stack.insert(v);

        for &(_, w) in &st.adj[v] {
            if !st.nodes.contains(&w) {
                continue;
            }
            if !st.indices.contains_key(&w) {
                strongconnect(w, st);
                let lw = st.lowlink[&w];
                let lv = st.lowlink[&v];
                if lw < lv {
                    st.lowlink.insert(v, lw);
                }
            } else if st.on_stack.contains(&w) {
                let iw = st.indices[&w];
                let lv = st.lowlink[&v];
                if iw < lv {
                    st.lowlink.insert(v, iw);
                }
            }
        }

        if st.lowlink[&v] == st.indices[&v] {
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

    for &n in nodes {
        if !st.indices.contains_key(&n) {
            strongconnect(n, &mut st);
        }
    }

    st.sccs
}

/// Report from Symbolic Bounded Model Checking (`P3.2`) unrolling a `system` up to depth `k` in SMT-LIB2.
#[derive(Debug, Clone, Serialize)]
pub struct SymbolicBmcReport {
    pub system_name: String,
    pub depth_k: usize,
    pub smt2_script: String,
    pub verdict: crate::smt::Verdict,
    pub prover: String,
    pub safe_up_to_k: bool,
}

fn step_var_map(states: &[StateVarDecl], step: usize) -> BTreeMap<String, Expr> {
    let mut map = BTreeMap::new();
    for st in states {
        map.insert(st.name.clone(), Expr::Var(format!("{}__{}", st.name, step)));
    }
    map
}

/// Emits an SMT-LIB2 Bounded Model Checking (BMC) refutation script unrolling `sys` for `k` transitions.
/// Checks whether any safety invariant can be violated at any step $t \in 0..=k$.
pub fn emit_symbolic_bmc_smt2(
    sys: &SystemDecl,
    ontology: &OntologyRegistry,
    k: usize,
) -> Option<String> {
    if sys.invariants.is_empty() || sys.states.is_empty() {
        return None;
    }

    let mut lines = vec![
        format!(";; Symbolic Bounded Model Checking (BMC) for system `{}` (depth k = {})", sys.name, k),
        "(set-logic ALL)".to_string(),
    ];

    // Declare state variables for steps 0..=k
    for step in 0..=k {
        for st in &sys.states {
            let smt_sort = match &st.ty {
                TypeExpr::Named(n) if n == "Int" || n == "Integer" => "Int",
                TypeExpr::Named(n) if n == "Bool" || n == "Boolean" => "Bool",
                _ => return None,
            };
            lines.push(format!("(declare-const {}__{} {})", st.name, step, smt_sort));
        }
    }

    // Assert initial state at step 0
    let map0 = step_var_map(&sys.states, 0);
    for st in &sys.states {
        let init_e = subst_expr(&st.init, &map0);
        let init_smt = crate::smt::expr_to_smt(&init_e, ontology, None)?;
        lines.push(format!("(assert (= {}__0 {}))", st.name, init_smt));
    }

    // Assert transition relation T(s_t, s_{t+1}) for each step t in 0..k
    for step in 0..k {
        let cur_map = step_var_map(&sys.states, step);
        let mut disjuncts = Vec::new();
        let mut guards_smt = Vec::new();

        for tr in &sys.transitions {
            let g_sub = subst_expr(&tr.guard, &cur_map);
            let g_smt = crate::smt::expr_to_smt(&g_sub, ontology, None)?;
            guards_smt.push(g_smt.clone());

            let mut branch_conjuncts = vec![g_smt];
            let mut updated_vars = BTreeSet::new();
            for (vname, uexpr) in &tr.updates {
                updated_vars.insert(vname.as_str());
                let u_sub = subst_expr(uexpr, &cur_map);
                let u_smt = crate::smt::expr_to_smt(&u_sub, ontology, None)?;
                branch_conjuncts.push(format!("(= {}__{} {})", vname, step + 1, u_smt));
            }
            // Frame condition for unmodified state variables
            for st in &sys.states {
                if !updated_vars.contains(st.name.as_str()) {
                    branch_conjuncts.push(format!(
                        "(= {}__{} {}__{})",
                        st.name,
                        step + 1,
                        st.name,
                        step
                    ));
                }
            }
            disjuncts.push(format!("(and {})", branch_conjuncts.join(" ")));
        }

        // Stuttering step when no guard is enabled (terminal state)
        if !guards_smt.is_empty() {
            let not_bb = format!("(not (or {}))", guards_smt.join(" "));
            let mut stutter = vec![not_bb];
            for st in &sys.states {
                stutter.push(format!("(= {}__{} {}__{})", st.name, step + 1, st.name, step));
            }
            disjuncts.push(format!("(and {})", stutter.join(" ")));
        }

        if !disjuncts.is_empty() {
            lines.push(format!("(assert (or {}))", disjuncts.join(" ")));
        }
    }

    // Assert negation of safety invariants across steps 0..=k
    let mut all_step_invs = Vec::new();
    for step in 0..=k {
        let map_t = step_var_map(&sys.states, step);
        for inv in &sys.invariants {
            let inv_sub = subst_expr(&inv.formula, &map_t);
            let inv_smt = crate::smt::expr_to_smt(&inv_sub, ontology, None)?;
            all_step_invs.push(inv_smt);
        }
    }
    lines.push(format!(
        "(assert (not (and {})))",
        all_step_invs.join(" ")
    ));
    lines.push("(check-sat)".to_string());

    Some(lines.join("\n") + "\n")
}

/// Runs Symbolic Bounded Model Checking (`P3.2`) for a single `system` up to depth `k`.
pub fn symbolic_bmc_system(
    sys: &SystemDecl,
    ontology: &OntologyRegistry,
    k: usize,
    prover: crate::smt::Prover,
) -> Option<SymbolicBmcReport> {
    let smt2_script = emit_symbolic_bmc_smt2(sys, ontology, k)?;
    let res = crate::smt::run_smt_prover(prover, &smt2_script);
    let safe_up_to_k = res.verdict == crate::smt::Verdict::Inconsistent;
    Some(SymbolicBmcReport {
        system_name: sys.name.clone(),
        depth_k: k,
        smt2_script,
        verdict: res.verdict,
        prover: res.prover,
        safe_up_to_k,
    })
}

/// Runs Symbolic Bounded Model Checking (`P3.2`) for all `system` declarations in `program` that use `Int`/`Bool` state sorts.
pub fn symbolic_bmc_program(
    program: &Program,
    ontology: &OntologyRegistry,
    k: usize,
    prover: crate::smt::Prover,
) -> Vec<SymbolicBmcReport> {
    let mut reports = Vec::new();
    for item in &program.items {
        if let Item::System(sys) = item {
            if let Some(rep) = symbolic_bmc_system(sys, ontology, k, prover) {
                reports.push(rep);
            }
        }
    }
    reports
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    fn key(v: &Value) -> String {
        let mut out = String::new();
        encode_value_canonical(v, &mut out);
        out
    }

    fn list(items: Vec<Value>) -> Value {
        Value::List(Rc::new(items))
    }

    fn record(concept: &str, fields: &[(&str, Value)]) -> Value {
        Value::ConceptInstance {
            concept: concept.into(),
            fields: fields
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect(),
        }
    }

    /// Structurally different values must never share a state key, or BFS would treat an
    /// unexplored state as visited and report VERIFIED without checking it.
    #[test]
    fn canonical_keys_are_distinct_for_distinct_values() {
        let values = vec![
            Value::Int(1),
            Value::Int(12),
            Value::Float(1.0),
            Value::Float(0.0),
            Value::Float(-0.0),
            Value::Bool(true),
            Value::Str("1".into()),
            Value::Str("1;".into()),
            Value::Str("".into()),
            Value::Unit,
            list(vec![]),
            list(vec![Value::Int(1), Value::Int(2)]),
            list(vec![Value::Int(12)]),
            list(vec![Value::Int(1), list(vec![Value::Int(2)])]),
            list(vec![list(vec![Value::Int(1)]), Value::Int(2)]),
            list(vec![list(vec![Value::Int(1), Value::Int(2)])]),
            list(vec![list(vec![]), list(vec![])]),
            list(vec![list(vec![list(vec![])])]),
            record("P", &[("a", Value::Int(1)), ("b", Value::Int(2))]),
            record("P", &[("a", Value::Int(2)), ("b", Value::Int(1))]),
            record("P", &[("ab", Value::Int(1))]),
            record("Q", &[("a", Value::Int(1)), ("b", Value::Int(2))]),
            record("P", &[]),
            Value::AdtVariant {
                variant: "Some".into(),
                fields: vec![Value::Int(1)],
            },
            Value::AdtVariant {
                variant: "Some".into(),
                fields: vec![],
            },
            Value::AdtVariant {
                variant: "S".into(),
                fields: vec![Value::Str("ome".into())],
            },
            Value::PartialCall {
                func: "f".into(),
                args: vec![Some(Value::Int(1)), None],
            },
            Value::PartialCall {
                func: "f".into(),
                args: vec![None, Some(Value::Int(1))],
            },
            Value::PartialCall {
                func: "f".into(),
                args: vec![None],
            },
        ];
        for (i, a) in values.iter().enumerate() {
            assert_eq!(
                key(a),
                key(&a.clone()),
                "key must be deterministic for {a:?}"
            );
            for b in &values[i + 1..] {
                assert_ne!(key(a), key(b), "collision between {a:?} and {b:?}");
            }
        }
    }

    #[test]
    fn state_keys_separate_variable_boundaries() {
        // { a = "x;b=1", } vs { a = "x", b = 1 } and similar splits must stay distinct.
        let mut s1 = BTreeMap::new();
        s1.insert("a".to_string(), Value::Str("x; b=1".into()));
        let mut s2 = BTreeMap::new();
        s2.insert("a".to_string(), Value::Str("x".into()));
        s2.insert("b".to_string(), Value::Int(1));
        let mut s3 = BTreeMap::new();
        s3.insert("ab".to_string(), Value::Int(1));
        let mut s4 = BTreeMap::new();
        s4.insert("a".to_string(), list(vec![Value::Int(1)]));
        s4.insert("b".to_string(), list(vec![]));
        let mut s5 = BTreeMap::new();
        s5.insert("a".to_string(), list(vec![]));
        s5.insert("b".to_string(), list(vec![Value::Int(1)]));
        let keys: Vec<String> = [&s1, &s2, &s3, &s4, &s5]
            .iter()
            .map(|s| collision_free_state_key(s))
            .collect();
        for i in 0..keys.len() {
            for j in i + 1..keys.len() {
                assert_ne!(keys[i], keys[j], "states {i} and {j} collide");
            }
        }
    }
}
