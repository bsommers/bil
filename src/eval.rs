use crate::ast::*;
use crate::ontology::OntologyRegistry;
use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Unit,
    List(Rc<Vec<Value>>),
    ConceptInstance {
        concept: String,
        fields: BTreeMap<String, Value>,
    },
    AdtVariant {
        variant: String,
        fields: Vec<Value>,
    },
    PartialCall {
        func: String,
        args: Vec<Option<Value>>,
    },
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(v) => write!(f, "{}", v),
            Value::Float(v) => write!(f, "{}", v),
            Value::Bool(v) => write!(f, "{}", v),
            Value::Str(v) => write!(f, "\"{}\"", v),
            Value::Unit => write!(f, "()"),
            Value::List(items) => {
                let s: Vec<String> = items.iter().map(|i| i.to_string()).collect();
                write!(f, "[{}]", s.join(", "))
            }
            Value::ConceptInstance { concept, fields } => {
                let s: Vec<String> = fields
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v))
                    .collect();
                write!(f, "{} {{ {} }}", concept, s.join(", "))
            }
            Value::AdtVariant { variant, fields } => {
                if fields.is_empty() {
                    write!(f, "{}", variant)
                } else {
                    let s: Vec<String> = fields.iter().map(|v| v.to_string()).collect();
                    write!(f, "{}({})", variant, s.join(", "))
                }
            }
            Value::PartialCall { func, .. } => write!(f, "<partial {}>", func),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RuntimeError {
    pub message: String,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[RuntimeError] {}", self.message)
    }
}

#[derive(Debug, Clone)]
pub struct Interpreter {
    pub ontology: OntologyRegistry,
    pub functions: BTreeMap<String, FnDecl>,
    pub specs: BTreeMap<String, SpecDecl>,
    pub axioms: Vec<AxiomDecl>,
    pub adt_variants: BTreeMap<String, usize>,
    pub globals: BTreeMap<String, Value>,
    pub concept_store: BTreeMap<String, Vec<Value>>,
    pub rng_state: u64,
    pub trace_enabled: bool,
    pub trace_log: Vec<String>,
}

impl Interpreter {
    pub fn new(ontology: OntologyRegistry, seed: u64, trace_enabled: bool) -> Self {
        Self {
            ontology,
            functions: BTreeMap::new(),
            specs: BTreeMap::new(),
            axioms: Vec::new(),
            adt_variants: BTreeMap::new(),
            globals: BTreeMap::new(),
            concept_store: BTreeMap::new(),
            rng_state: if seed == 0 { 0x9E3779B97F4A7C15 } else { seed },
            trace_enabled,
            trace_log: Vec::new(),
        }
    }

    pub fn next_rand_index(&mut self, len: usize) -> usize {
        if len <= 1 {
            return 0;
        }
        // Xorshift64* deterministic PRNG for reproducible nondeterministic guard choice
        let mut x = self.rng_state;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.rng_state = x;
        let r = x.wrapping_mul(0x2545F4914F6CDD1D);
        (r as usize) % len
    }

    pub fn register_instance(&mut self, val: &Value) {
        match val {
            Value::ConceptInstance { concept, .. } => {
                let list = self.concept_store.entry(concept.clone()).or_default();
                if !list.contains(val) {
                    list.push(val.clone());
                }
            }
            Value::List(items) => {
                for item in items.iter() {
                    self.register_instance(item);
                }
            }
            _ => {}
        }
    }

    pub fn instances_of(&self, concept: &str) -> Vec<Value> {
        let mut out = Vec::new();
        for (cname, items) in &self.concept_store {
            if self.ontology.is_subconcept(cname, concept) {
                for item in items {
                    if !out.contains(item) {
                        out.push(item.clone());
                    }
                }
            }
        }
        out
    }

    pub fn run_program(&mut self, program: &Program) -> Result<Vec<(String, Value)>, RuntimeError> {
        for item in &program.items {
            match item {
                Item::TypeDecl(adt) => {
                    for v in &adt.variants {
                        self.adt_variants.insert(v.name.clone(), v.payload.len());
                        if v.payload.is_empty() {
                            self.globals.insert(
                                v.name.clone(),
                                Value::AdtVariant {
                                    variant: v.name.clone(),
                                    fields: vec![],
                                },
                            );
                        }
                    }
                }
                Item::Spec(sp) => {
                    self.specs.insert(sp.name.clone(), sp.clone());
                }
                Item::FnDecl(f) => {
                    self.functions.insert(f.name.clone(), f.clone());
                }
                Item::Axiom(ax) => {
                    self.axioms.push(ax.clone());
                }
                _ => {}
            }
        }

        let mut outputs = Vec::new();
        for item in &program.items {
            match item {
                Item::Let(l) => {
                    let env = self.globals.clone();
                    let val = self.eval_expr(&l.value, &env)?;
                    self.register_instance(&val);
                    self.globals.insert(l.name.clone(), val.clone());
                    outputs.push((l.name.clone(), val));
                }
                Item::Assert(a) => {
                    let env = self.globals.clone();
                    let v = self.eval_expr(&a.formula, &env)?;
                    if v != Value::Bool(true) {
                        return Err(RuntimeError {
                            message: format!(
                                "Assertion failed at line {}: {:?}",
                                a.span.line, a.formula
                            ),
                        });
                    }
                }
                _ => {}
            }
        }

        // Verify all OntoLogic domain axioms over populated concept store
        self.check_axioms()?;

        Ok(outputs)
    }

    pub fn check_axioms(&mut self) -> Result<(), RuntimeError> {
        let axioms = self.axioms.clone();
        let env = self.globals.clone();
        for ax in axioms {
            let res = self.eval_expr(&ax.formula, &env)?;
            if res != Value::Bool(true) {
                return Err(RuntimeError {
                    message: format!(
                        "OntoLogic Axiom '{}' violated at line {}",
                        ax.name, ax.span.line
                    ),
                });
            }
        }
        Ok(())
    }

    pub fn eval_expr(
        &mut self,
        expr: &Expr,
        env: &BTreeMap<String, Value>,
    ) -> Result<Value, RuntimeError> {
        match expr {
            Expr::Int(v) => Ok(Value::Int(*v)),
            Expr::Float(v) => Ok(Value::Float(*v)),
            Expr::Bool(v) => Ok(Value::Bool(*v)),
            Expr::Str(v) => Ok(Value::Str(v.clone())),
            Expr::Placeholder => env.get("_").cloned().ok_or_else(|| RuntimeError {
                message: "Unbound placeholder '_'".into(),
            }),
            Expr::Var(name) => {
                if let Some(v) = env.get(name) {
                    Ok(v.clone())
                } else if let Some(v) = self.globals.get(name) {
                    Ok(v.clone())
                } else if self.ontology.concepts.contains_key(name) {
                    Ok(Value::List(Rc::new(self.instances_of(name))))
                } else {
                    Err(RuntimeError {
                        message: format!("Unbound variable '{}'", name),
                    })
                }
            }
            Expr::Unary { op, expr: inner } => {
                let v = self.eval_expr(inner, env)?;
                match (op, v) {
                    (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                    (UnaryOp::Neg, Value::Int(i)) => Ok(Value::Int(-i)),
                    (UnaryOp::Neg, Value::Float(f)) => Ok(Value::Float(-f)),
                    (_, other) => Err(RuntimeError {
                        message: format!("Invalid unary operation on {}", other),
                    }),
                }
            }
            Expr::Binary { op, left, right } => {
                if *op == BinOp::Pipe {
                    let lv = self.eval_expr(left, env)?;
                    return self.eval_pipe(lv, right, env);
                }
                // Short-circuit logical operators
                if *op == BinOp::And {
                    let lv = self.eval_expr(left, env)?;
                    if lv == Value::Bool(false) {
                        return Ok(Value::Bool(false));
                    }
                    return self.eval_expr(right, env);
                }
                if *op == BinOp::Or {
                    let lv = self.eval_expr(left, env)?;
                    if lv == Value::Bool(true) {
                        return Ok(Value::Bool(true));
                    }
                    return self.eval_expr(right, env);
                }
                if *op == BinOp::Implies {
                    let lv = self.eval_expr(left, env)?;
                    if lv == Value::Bool(false) {
                        return Ok(Value::Bool(true));
                    }
                    return self.eval_expr(right, env);
                }

                let lv = self.eval_expr(left, env)?;
                let rv = self.eval_expr(right, env)?;

                match (op, lv, rv) {
                    (BinOp::Iff, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
                    (BinOp::Eq, a, b) => Ok(Value::Bool(a == b)),
                    (BinOp::Neq, a, b) => Ok(Value::Bool(a != b)),
                    (BinOp::Lt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
                    (BinOp::Le, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
                    (BinOp::Gt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
                    (BinOp::Ge, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
                    (BinOp::Lt, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
                    (BinOp::Le, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
                    (BinOp::Gt, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
                    (BinOp::Ge, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
                    (BinOp::In, elem, Value::List(list)) => Ok(Value::Bool(list.contains(&elem))),
                    (BinOp::Range, Value::Int(a), Value::Int(b)) => {
                        let items: Vec<Value> = (a..b).map(Value::Int).collect();
                        Ok(Value::List(Rc::new(items)))
                    }
                    (BinOp::RangeInc, Value::Int(a), Value::Int(b)) => {
                        let items: Vec<Value> = (a..=b).map(Value::Int).collect();
                        Ok(Value::List(Rc::new(items)))
                    }
                    (BinOp::Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
                    (BinOp::Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
                    (BinOp::Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
                    (BinOp::Div, Value::Int(a), Value::Int(b)) => {
                        if b == 0 {
                            Err(RuntimeError {
                                message: "Division by zero".into(),
                            })
                        } else {
                            Ok(Value::Int(a / b))
                        }
                    }
                    (BinOp::Mod, Value::Int(a), Value::Int(b)) => {
                        if b == 0 {
                            Err(RuntimeError {
                                message: "Modulo by zero".into(),
                            })
                        } else {
                            Ok(Value::Int(a % b))
                        }
                    }
                    (BinOp::Add, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
                    (BinOp::Sub, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
                    (BinOp::Mul, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
                    (BinOp::Div, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
                    (BinOp::Add, Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{}{}", a, b))),
                    (op, l, r) => Err(RuntimeError {
                        message: format!("Unsupported binary op {} on {} and {}", op, l, r),
                    }),
                }
            }
            Expr::Quantifier {
                kind,
                var,
                domain,
                body,
            } => {
                let dom_val = self.eval_expr(domain, env)?;
                let items = match dom_val {
                    Value::List(list) => list,
                    other => {
                        return Err(RuntimeError {
                            message: format!("Quantifier domain must be a list, got {}", other),
                        })
                    }
                };
                match kind {
                    QuantifierKind::Forall => {
                        for item in items.iter() {
                            let mut inner_env = env.clone();
                            inner_env.insert(var.clone(), item.clone());
                            if self.eval_expr(body, &inner_env)? != Value::Bool(true) {
                                return Ok(Value::Bool(false));
                            }
                        }
                        Ok(Value::Bool(true))
                    }
                    QuantifierKind::Exists => {
                        for item in items.iter() {
                            let mut inner_env = env.clone();
                            inner_env.insert(var.clone(), item.clone());
                            if self.eval_expr(body, &inner_env)? == Value::Bool(true) {
                                return Ok(Value::Bool(true));
                            }
                        }
                        Ok(Value::Bool(false))
                    }
                    QuantifierKind::Choose => {
                        let mut candidates = Vec::new();
                        for item in items.iter() {
                            let mut inner_env = env.clone();
                            inner_env.insert(var.clone(), item.clone());
                            if self.eval_expr(body, &inner_env)? == Value::Bool(true) {
                                candidates.push(item.clone());
                            }
                        }
                        if candidates.is_empty() {
                            return Err(RuntimeError {
                                message: format!(
                                    "Nondeterministic 'choose {}' aborted: no element satisfies predicate",
                                    var
                                ),
                            });
                        }
                        let idx = self.next_rand_index(candidates.len());
                        let chosen = candidates[idx].clone();
                        if self.trace_enabled && candidates.len() > 1 {
                            self.trace_log.push(format!(
                                "[choose {}] {} candidates enabled -> selected {}",
                                var,
                                candidates.len(),
                                chosen
                            ));
                        }
                        Ok(chosen)
                    }
                }
            }
            Expr::IfFi { branches } => {
                // True Dijkstra Nondeterminism: evaluate ALL guards first, collect all enabled branches
                let mut enabled = Vec::new();
                for (idx, br) in branches.iter().enumerate() {
                    let g = self.eval_expr(&br.guard, env)?;
                    if g == Value::Bool(true) {
                        enabled.push((idx, br));
                    }
                }
                if enabled.is_empty() {
                    return Err(RuntimeError {
                        message: "Dijkstra 'if ... fi' ABORT: no guard evaluated to true (¬BB)"
                            .into(),
                    });
                }
                let pick = self.next_rand_index(enabled.len());
                let (chosen_idx, chosen_br) = enabled[pick];
                if self.trace_enabled && enabled.len() > 1 {
                    let indices: Vec<String> =
                        enabled.iter().map(|(i, _)| format!("#{}", i + 1)).collect();
                    self.trace_log.push(format!(
                        "[if..fi] nondeterministic choice among guards [{}] -> picked #{}",
                        indices.join(", "),
                        chosen_idx + 1
                    ));
                }
                match &chosen_br.body {
                    GclBody::Expr(e) => self.eval_expr(e, env),
                    GclBody::Skip => Ok(Value::Unit),
                    GclBody::Abort => Err(RuntimeError {
                        message: "Explicit GCL 'abort' executed".into(),
                    }),
                    GclBody::Updates(_) => Ok(Value::Unit),
                }
            }
            Expr::DoOd {
                inits,
                invariant,
                variant,
                branches,
                then_expr,
            } => {
                let mut loop_env = env.clone();
                for (vname, init_expr) in inits {
                    let val = self.eval_expr(init_expr, &loop_env)?;
                    loop_env.insert(vname.clone(), val);
                }

                // Check initial invariant: Pre => I
                if let Some(inv) = invariant {
                    if self.eval_expr(inv, &loop_env)? != Value::Bool(true) {
                        return Err(RuntimeError {
                            message: "GCL 'do ... od' loop invariant violated on initialization"
                                .into(),
                        });
                    }
                }

                let mut step = 0usize;
                loop {
                    // Evaluate all guards simultaneously (Dijkstra semantics)
                    let mut enabled = Vec::new();
                    for (idx, br) in branches.iter().enumerate() {
                        if self.eval_expr(&br.guard, &loop_env)? == Value::Bool(true) {
                            enabled.push((idx, br));
                        }
                    }

                    // Loop terminates when ¬BB (no guard holds)
                    if enabled.is_empty() {
                        break;
                    }

                    step += 1;
                    if step > 100_000 {
                        return Err(RuntimeError {
                            message: "GCL 'do ... od' exceeded maximum step bound (100,000)".into(),
                        });
                    }

                    // Record variant before transition: must be >= 0 when BB holds
                    let prev_variant = if let Some(var_expr) = variant {
                        match self.eval_expr(var_expr, &loop_env)? {
                            Value::Int(v) => {
                                if v < 0 {
                                    return Err(RuntimeError {
                                        message: format!(
                                            "GCL 'do ... od' variant became negative ({}) while guard enabled",
                                            v
                                        ),
                                    });
                                }
                                Some(v)
                            }
                            other => {
                                return Err(RuntimeError {
                                    message: format!("Loop variant must be Int, got {}", other),
                                })
                            }
                        }
                    } else {
                        None
                    };

                    // Nondeterministically choose one enabled guard
                    let pick = self.next_rand_index(enabled.len());
                    let (chosen_idx, chosen_br) = enabled[pick];
                    if self.trace_enabled && enabled.len() > 1 {
                        let indices: Vec<String> =
                            enabled.iter().map(|(i, _)| format!("#{}", i + 1)).collect();
                        self.trace_log.push(format!(
                            "[do..od step {}] nondeterministic choice among [{}] -> picked #{}",
                            step,
                            indices.join(", "),
                            chosen_idx + 1
                        ));
                    }

                    match &chosen_br.body {
                        GclBody::Updates(ups) => {
                            // Simultaneous state update
                            let mut next_vals = Vec::new();
                            for (vname, uexpr) in ups {
                                let nv = self.eval_expr(uexpr, &loop_env)?;
                                next_vals.push((vname.clone(), nv));
                            }
                            for (vname, nv) in next_vals {
                                loop_env.insert(vname, nv);
                            }
                        }
                        GclBody::Expr(e) => {
                            let nv = self.eval_expr(e, &loop_env)?;
                            loop_env.insert(inits[0].0.clone(), nv);
                        }
                        GclBody::Skip => {}
                        GclBody::Abort => {
                            return Err(RuntimeError {
                                message: "Explicit GCL 'abort' inside 'do ... od'".into(),
                            });
                        }
                    }

                    // Verify invariant preservation: I ∧ G => wp(S, I)
                    if let Some(inv) = invariant {
                        if self.eval_expr(inv, &loop_env)? != Value::Bool(true) {
                            return Err(RuntimeError {
                                message: format!(
                                    "GCL 'do ... od' loop invariant violated after branch #{}",
                                    chosen_idx + 1
                                ),
                            });
                        }
                    }

                    // Verify strict variant decrease: V_next < V_prev
                    if let (Some(prev_v), Some(var_expr)) = (prev_variant, variant) {
                        if let Value::Int(next_v) = self.eval_expr(var_expr, &loop_env)? {
                            if next_v >= prev_v {
                                return Err(RuntimeError {
                                    message: format!(
                                        "GCL 'do ... od' variant failed to decrease: {} -> {}",
                                        prev_v, next_v
                                    ),
                                });
                            }
                        }
                    }
                }

                self.eval_expr(then_expr, &loop_env)
            }
            Expr::Match { scrutinee, arms } => {
                let val = self.eval_expr(scrutinee, env)?;
                for arm in arms {
                    if let Some(bindings) = match_pattern(&arm.pattern, &val) {
                        let mut arm_env = env.clone();
                        for (k, v) in bindings {
                            arm_env.insert(k, v);
                        }
                        return self.eval_expr(&arm.body, &arm_env);
                    }
                }
                Err(RuntimeError {
                    message: format!("Non-exhaustive match at runtime for value {}", val),
                })
            }
            Expr::RecordInit { concept, fields } => {
                let mut fmap = BTreeMap::new();
                for (k, e) in fields {
                    let v = self.eval_expr(e, env)?;
                    fmap.insert(k.clone(), v);
                }
                let inst = Value::ConceptInstance {
                    concept: concept.clone(),
                    fields: fmap,
                };
                self.register_instance(&inst);
                Ok(inst)
            }
            Expr::RecordWith { base, updates } => {
                let base_val = self.eval_expr(base, env)?;
                match base_val {
                    Value::ConceptInstance {
                        concept,
                        mut fields,
                    } => {
                        for (k, ue) in updates {
                            let nv = self.eval_expr(ue, env)?;
                            fields.insert(k.clone(), nv);
                        }
                        let inst = Value::ConceptInstance { concept, fields };
                        self.register_instance(&inst);
                        Ok(inst)
                    }
                    other => Err(RuntimeError {
                        message: format!("Cannot apply 'with' to {}", other),
                    }),
                }
            }
            Expr::FieldAccess { base, field } => {
                let base_val = self.eval_expr(base, env)?;
                match base_val {
                    Value::ConceptInstance { fields, concept } => {
                        fields.get(field).cloned().ok_or_else(|| RuntimeError {
                            message: format!("Field '{}' not found on '{}'", field, concept),
                        })
                    }
                    other => Err(RuntimeError {
                        message: format!("Cannot access field '{}' on {}", field, other),
                    }),
                }
            }
            Expr::Call { func, args } => {
                // Check for partial application placeholders `_` when `_` is not bound
                let has_unbound_placeholder =
                    args.iter().any(|a| matches!(a, Expr::Placeholder)) && !env.contains_key("_");
                if has_unbound_placeholder {
                    let mut pargs = Vec::new();
                    for a in args {
                        if matches!(a, Expr::Placeholder) {
                            pargs.push(None);
                        } else {
                            pargs.push(Some(self.eval_expr(a, env)?));
                        }
                    }
                    return Ok(Value::PartialCall {
                        func: func.clone(),
                        args: pargs,
                    });
                }

                let mut eval_args = Vec::new();
                for a in args {
                    eval_args.push(self.eval_expr(a, env)?);
                }
                self.invoke_function(func, eval_args)
            }
            Expr::List(items) => {
                let mut vals = Vec::new();
                for item in items {
                    vals.push(self.eval_expr(item, env)?);
                }
                let list = Value::List(Rc::new(vals));
                self.register_instance(&list);
                Ok(list)
            }
            Expr::LetIn { name, value, body } => {
                let v = self.eval_expr(value, env)?;
                let mut inner_env = env.clone();
                inner_env.insert(name.clone(), v);
                self.eval_expr(body, &inner_env)
            }
        }
    }

    pub fn invoke_function(
        &mut self,
        func: &str,
        args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        match func {
            "min" if args.len() == 2 => match (&args[0], &args[1]) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int((*a).min(*b))),
                _ => Err(RuntimeError {
                    message: "min expects two Ints".into(),
                }),
            },
            "max" if args.len() == 2 => match (&args[0], &args[1]) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int((*a).max(*b))),
                _ => Err(RuntimeError {
                    message: "max expects two Ints".into(),
                }),
            },
            "abs" if args.len() == 1 => match &args[0] {
                Value::Int(a) => Ok(Value::Int(a.abs())),
                _ => Err(RuntimeError {
                    message: "abs expects an Int".into(),
                }),
            },
            "count" if args.len() == 1 => match &args[0] {
                Value::List(items) => Ok(Value::Int(items.len() as i64)),
                _ => Err(RuntimeError {
                    message: "count expects a List".into(),
                }),
            },
            "sum" if args.len() == 1 => match &args[0] {
                Value::List(items) => {
                    let mut total = 0i64;
                    for item in items.iter() {
                        if let Value::Int(v) = item {
                            total += v;
                        }
                    }
                    Ok(Value::Int(total))
                }
                _ => Err(RuntimeError {
                    message: "sum expects List<Int>".into(),
                }),
            },
            "is_a" if args.len() == 2 => match (&args[0], &args[1]) {
                (Value::ConceptInstance { concept, .. }, Value::Str(target)) => {
                    Ok(Value::Bool(self.ontology.is_subconcept(concept, target)))
                }
                _ => Ok(Value::Bool(false)),
            },
            _ => {
                if self.adt_variants.contains_key(func) {
                    return Ok(Value::AdtVariant {
                        variant: func.to_string(),
                        fields: args,
                    });
                }

                let fdecl = self.functions.get(func).cloned().ok_or_else(|| RuntimeError {
                    message: format!("Undefined function '{}'", func),
                })?;

                let mut fn_env = BTreeMap::new();
                for (param, arg_val) in fdecl.params.iter().zip(args.iter()) {
                    fn_env.insert(param.name.clone(), arg_val.clone());
                }

                // Check function precondition (`requires`)
                if let Some(req) = &fdecl.requires {
                    if self.eval_expr(req, &fn_env)? != Value::Bool(true) {
                        return Err(RuntimeError {
                            message: format!(
                                "Precondition ('requires') violated calling '{}'",
                                func
                            ),
                        });
                    }
                }

                // If function refines a spec, check spec precondition too
                if let Some(spec_name) = &fdecl.refines {
                    if let Some(spec) = self.specs.get(spec_name).cloned() {
                        if let Some(sreq) = &spec.requires {
                            if self.eval_expr(sreq, &fn_env)? != Value::Bool(true) {
                                return Err(RuntimeError {
                                    message: format!(
                                        "Refined spec '{}' precondition violated calling '{}'",
                                        spec_name, func
                                    ),
                                });
                            }
                        }
                    }
                }

                let result = self.eval_expr(&fdecl.body, &fn_env)?;
                self.register_instance(&result);

                // Check function postcondition (`ensures`)
                if let Some(ens) = &fdecl.ensures {
                    let mut post_env = fn_env.clone();
                    post_env.insert("result".into(), result.clone());
                    if self.eval_expr(ens, &post_env)? != Value::Bool(true) {
                        return Err(RuntimeError {
                            message: format!(
                                "Postcondition ('ensures') violated in '{}' with result {}",
                                func, result
                            ),
                        });
                    }
                }

                // Check refined spec postcondition (`refines`)
                if let Some(spec_name) = &fdecl.refines {
                    if let Some(spec) = self.specs.get(spec_name).cloned() {
                        if let Some(sens) = &spec.ensures {
                            let mut post_env = fn_env;
                            post_env.insert("result".into(), result.clone());
                            if self.eval_expr(sens, &post_env)? != Value::Bool(true) {
                                return Err(RuntimeError {
                                    message: format!(
                                        "Refinement contract '{}' postcondition violated by '{}' with result {}",
                                        spec_name, func, result
                                    ),
                                });
                            }
                        }
                    }
                }

                Ok(result)
            }
        }
    }

    fn eval_pipe(
        &mut self,
        left_val: Value,
        right: &Expr,
        env: &BTreeMap<String, Value>,
    ) -> Result<Value, RuntimeError> {
        if let Expr::Call { func, args } = right {
            match func.as_str() {
                "where" | "filter" if args.len() == 1 => {
                    let items = match left_val {
                        Value::List(l) => l,
                        other => {
                            return Err(RuntimeError {
                                message: format!("'where' expects List, got {}", other),
                            })
                        }
                    };
                    let mut out = Vec::new();
                    for item in items.iter() {
                        let mut penv = env.clone();
                        penv.insert("_".into(), item.clone());
                        let keep = match self.eval_expr(&args[0], &penv)? {
                            Value::Bool(b) => b,
                            Value::PartialCall {
                                func: pfn,
                                args: pargs,
                            } => {
                                let filled = fill_partial(&pargs, item.clone());
                                self.invoke_function(&pfn, filled)? == Value::Bool(true)
                            }
                            other => {
                                return Err(RuntimeError {
                                    message: format!("Predicate returned non-Bool: {}", other),
                                })
                            }
                        };
                        if keep {
                            out.push(item.clone());
                        }
                    }
                    return Ok(Value::List(Rc::new(out)));
                }
                "map" | "select" if args.len() == 1 => {
                    let items = match left_val {
                        Value::List(l) => l,
                        other => {
                            return Err(RuntimeError {
                                message: format!("'map' expects List, got {}", other),
                            })
                        }
                    };
                    let mut out = Vec::new();
                    for item in items.iter() {
                        let mut menv = env.clone();
                        menv.insert("_".into(), item.clone());
                        let mapped = match self.eval_expr(&args[0], &menv)? {
                            Value::PartialCall {
                                func: pfn,
                                args: pargs,
                            } => {
                                let filled = fill_partial(&pargs, item.clone());
                                self.invoke_function(&pfn, filled)?
                            }
                            val => val,
                        };
                        self.register_instance(&mapped);
                        out.push(mapped);
                    }
                    return Ok(Value::List(Rc::new(out)));
                }
                "sort_by" if args.len() == 1 => {
                    let items = match left_val {
                        Value::List(l) => l,
                        other => {
                            return Err(RuntimeError {
                                message: format!("'sort_by' expects List, got {}", other),
                            })
                        }
                    };
                    let mut keyed = Vec::new();
                    for item in items.iter() {
                        let mut kenv = env.clone();
                        kenv.insert("_".into(), item.clone());
                        let k = self.eval_expr(&args[0], &kenv)?;
                        keyed.push((k, item.clone()));
                    }
                    keyed.sort_by(|(ka, _), (kb, _)| match (ka, kb) {
                        (Value::Int(a), Value::Int(b)) => a.cmp(b),
                        (Value::Str(a), Value::Str(b)) => a.cmp(b),
                        _ => std::cmp::Ordering::Equal,
                    });
                    let sorted: Vec<Value> = keyed.into_iter().map(|(_, v)| v).collect();
                    return Ok(Value::List(Rc::new(sorted)));
                }
                "all" if args.len() == 1 => {
                    let items = match left_val {
                        Value::List(l) => l,
                        other => {
                            return Err(RuntimeError {
                                message: format!("'all' expects List, got {}", other),
                            })
                        }
                    };
                    for item in items.iter() {
                        let mut penv = env.clone();
                        penv.insert("_".into(), item.clone());
                        if self.eval_expr(&args[0], &penv)? != Value::Bool(true) {
                            return Ok(Value::Bool(false));
                        }
                    }
                    return Ok(Value::Bool(true));
                }
                "any" if args.len() == 1 => {
                    let items = match left_val {
                        Value::List(l) => l,
                        other => {
                            return Err(RuntimeError {
                                message: format!("'any' expects List, got {}", other),
                            })
                        }
                    };
                    for item in items.iter() {
                        let mut penv = env.clone();
                        penv.insert("_".into(), item.clone());
                        if self.eval_expr(&args[0], &penv)? == Value::Bool(true) {
                            return Ok(Value::Bool(true));
                        }
                    }
                    return Ok(Value::Bool(false));
                }
                "count" if args.is_empty() => {
                    return self.invoke_function("count", vec![left_val]);
                }
                "sum" if args.is_empty() => {
                    return self.invoke_function("sum", vec![left_val]);
                }
                _ => {
                    if args.iter().any(|a| matches!(a, Expr::Placeholder)) {
                        let mut penv = env.clone();
                        penv.insert("_".into(), left_val);
                        return self.eval_expr(right, &penv);
                    } else {
                        let mut call_args = vec![left_val];
                        for a in args {
                            call_args.push(self.eval_expr(a, env)?);
                        }
                        return self.invoke_function(func, call_args);
                    }
                }
            }
        } else if let Expr::Var(func) = right {
            return self.invoke_function(func, vec![left_val]);
        }

        Err(RuntimeError {
            message: "Invalid pipeline stage".into(),
        })
    }
}

fn fill_partial(args: &[Option<Value>], replacement: Value) -> Vec<Value> {
    let mut out = Vec::new();
    let mut used = false;
    for a in args {
        match a {
            Some(v) => out.push(v.clone()),
            None if !used => {
                used = true;
                out.push(replacement.clone());
            }
            None => out.push(Value::Unit),
        }
    }
    out
}

fn match_pattern(pat: &Pattern, val: &Value) -> Option<Vec<(String, Value)>> {
    match (pat, val) {
        (Pattern::Wildcard, _) => Some(vec![]),
        (Pattern::Var(v), other) => Some(vec![(v.clone(), other.clone())]),
        (Pattern::Int(a), Value::Int(b)) if a == b => Some(vec![]),
        (Pattern::Bool(a), Value::Bool(b)) if a == b => Some(vec![]),
        (Pattern::Str(a), Value::Str(b)) if a == b => Some(vec![]),
        (
            Pattern::Variant(vname, bindings),
            Value::AdtVariant {
                variant, fields, ..
            },
        ) if vname == variant && bindings.len() == fields.len() => {
            let mut out = Vec::new();
            for (b, fval) in bindings.iter().zip(fields.iter()) {
                if b != "_" {
                    out.push((b.clone(), fval.clone()));
                }
            }
            Some(out)
        }
        _ => None,
    }
}
