use crate::ast::{BinOp, Pattern, QuantifierKind, UnaryOp};
use crate::eval::Value;
use crate::ir::hir::HirProgram;
use crate::ir::lir::{LirAction, LirExpr, LirProgram};
use crate::ontology::OntologyRegistry;
use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;

/// Compact stack/register bytecode instruction compiled from Ghost-Erased LIR (`LirProgram`).
/// All ghost constructs (`axiom`, `spec`, `proof`, `requires`, `ensures`, `invariant`, `variant`)
/// have been erased prior to bytecode emission.
#[derive(Debug, Clone)]
pub enum BytecodeOp {
    PushInt(i64),
    PushFloat(f64),
    PushBool(bool),
    PushStr(String),
    LoadVar(String),
    StoreVar(String),
    PopVar(String),
    Unary(UnaryOp),
    Binary(BinOp),
    MakeList(usize),
    MakeStruct {
        concept: String,
        fields: Vec<String>,
    },
    UpdateStruct {
        fields: Vec<String>,
    },
    GetField(String),
    Call {
        func: String,
        argc: usize,
    },
    PipeStage {
        stage: String,
        arg: Option<LirExpr>,
    },
    GuardedSelect {
        branches: Vec<(Vec<BytecodeOp>, CompiledAction)>,
    },
    GuardedLoop {
        inits: Vec<(String, Vec<BytecodeOp>)>,
        branches: Vec<(Vec<BytecodeOp>, CompiledAction)>,
        then_code: Vec<BytecodeOp>,
    },
    Match {
        arms: Vec<(Pattern, Vec<BytecodeOp>)>,
    },
    Quantifier {
        kind: QuantifierKind,
        var: String,
        domain_code: Vec<BytecodeOp>,
        body_code: Vec<BytecodeOp>,
    },
    Return,
}

#[derive(Debug, Clone)]
pub enum CompiledAction {
    ReturnExpr(Vec<BytecodeOp>),
    AssignState(Vec<(String, Vec<BytecodeOp>)>),
    Nop,
    TrapAbort,
}

#[derive(Debug, Clone)]
pub struct CompiledFn {
    pub name: String,
    pub params: Vec<String>,
    pub code: Vec<BytecodeOp>,
}

#[derive(Debug, Clone)]
pub struct BytecodeProgram {
    pub functions: BTreeMap<String, CompiledFn>,
    pub globals: Vec<(String, Vec<BytecodeOp>)>,
    pub adt_variants: BTreeMap<String, usize>,
    pub erased_ghost_count: usize,
}

impl BytecodeProgram {
    pub fn compile(lir: &LirProgram, hir: &HirProgram) -> Self {
        let mut adt_variants = BTreeMap::new();
        for adt in &hir.adts {
            for (vname, payload) in &adt.variants {
                adt_variants.insert(vname.clone(), payload.len());
            }
        }

        let mut functions = BTreeMap::new();
        for f in &lir.functions {
            let mut code = Vec::new();
            compile_expr(&f.body, &mut code);
            code.push(BytecodeOp::Return);
            functions.insert(
                f.name.clone(),
                CompiledFn {
                    name: f.name.clone(),
                    params: f.params.iter().map(|(n, _)| n.clone()).collect(),
                    code,
                },
            );
        }

        let mut globals = Vec::new();
        for (gname, _, gexpr) in &lir.globals {
            let mut code = Vec::new();
            compile_expr(gexpr, &mut code);
            code.push(BytecodeOp::Return);
            globals.push((gname.clone(), code));
        }

        BytecodeProgram {
            functions,
            globals,
            adt_variants,
            erased_ghost_count: lir.erased_ghost_count,
        }
    }

    pub fn total_instructions(&self) -> usize {
        let fn_ins: usize = self.functions.values().map(|f| f.code.len()).sum();
        let gl_ins: usize = self.globals.iter().map(|(_, c)| c.len()).sum();
        fn_ins + gl_ins
    }
}

fn compile_expr(expr: &LirExpr, out: &mut Vec<BytecodeOp>) {
    match expr {
        LirExpr::Int(v) => out.push(BytecodeOp::PushInt(*v)),
        LirExpr::Float(v) => out.push(BytecodeOp::PushFloat(*v)),
        LirExpr::Bool(v) => out.push(BytecodeOp::PushBool(*v)),
        LirExpr::Str(s) => out.push(BytecodeOp::PushStr(s.clone())),
        LirExpr::Var(v) => out.push(BytecodeOp::LoadVar(v.clone())),
        LirExpr::Placeholder => out.push(BytecodeOp::LoadVar("_".into())),
        LirExpr::Unary(op, inner) => {
            compile_expr(inner, out);
            out.push(BytecodeOp::Unary(*op));
        }
        LirExpr::Binary(op, l, r) => {
            compile_expr(l, out);
            compile_expr(r, out);
            out.push(BytecodeOp::Binary(*op));
        }
        LirExpr::List(items) => {
            for it in items {
                compile_expr(it, out);
            }
            out.push(BytecodeOp::MakeList(items.len()));
        }
        LirExpr::StructInit { name, fields } => {
            let mut fnames = Vec::new();
            for (fname, fexpr) in fields {
                compile_expr(fexpr, out);
                fnames.push(fname.clone());
            }
            out.push(BytecodeOp::MakeStruct {
                concept: name.clone(),
                fields: fnames,
            });
        }
        LirExpr::StructUpdate { base, updates } => {
            compile_expr(base, out);
            let mut fnames = Vec::new();
            for (fname, uexpr) in updates {
                compile_expr(uexpr, out);
                fnames.push(fname.clone());
            }
            out.push(BytecodeOp::UpdateStruct { fields: fnames });
        }
        LirExpr::Field { base, field } => {
            compile_expr(base, out);
            out.push(BytecodeOp::GetField(field.clone()));
        }
        LirExpr::Call { func, args } => {
            for a in args {
                compile_expr(a, out);
            }
            out.push(BytecodeOp::Call {
                func: func.clone(),
                argc: args.len(),
            });
        }
        LirExpr::PipeStage { stage, input, arg } => {
            compile_expr(input, out);
            out.push(BytecodeOp::PipeStage {
                stage: stage.clone(),
                arg: arg.as_ref().map(|b| (**b).clone()),
            });
        }
        LirExpr::LetIn { name, value, body } => {
            compile_expr(value, out);
            out.push(BytecodeOp::StoreVar(name.clone()));
            compile_expr(body, out);
            out.push(BytecodeOp::PopVar(name.clone()));
        }
        LirExpr::GuardedSelect { branches } => {
            let mut brs = Vec::new();
            for (g, act) in branches {
                let mut gcode = Vec::new();
                compile_expr(g, &mut gcode);
                brs.push((gcode, compile_action(act)));
            }
            out.push(BytecodeOp::GuardedSelect { branches: brs });
        }
        LirExpr::GuardedLoop {
            inits,
            branches,
            then_expr,
        } => {
            let mut c_inits = Vec::new();
            for (v, ie) in inits {
                let mut ic = Vec::new();
                compile_expr(ie, &mut ic);
                c_inits.push((v.clone(), ic));
            }
            let mut c_brs = Vec::new();
            for (g, act) in branches {
                let mut gc = Vec::new();
                compile_expr(g, &mut gc);
                c_brs.push((gc, compile_action(act)));
            }
            let mut tc = Vec::new();
            compile_expr(then_expr, &mut tc);
            out.push(BytecodeOp::GuardedLoop {
                inits: c_inits,
                branches: c_brs,
                then_code: tc,
            });
        }
        LirExpr::Match { scrutinee, arms } => {
            compile_expr(scrutinee, out);
            let mut c_arms = Vec::new();
            for (pat, body) in arms {
                let mut bc = Vec::new();
                compile_expr(body, &mut bc);
                c_arms.push((pat.clone(), bc));
            }
            out.push(BytecodeOp::Match { arms: c_arms });
        }
        LirExpr::Quantifier {
            kind,
            var,
            domain,
            body,
        } => {
            let mut dc = Vec::new();
            compile_expr(domain, &mut dc);
            let mut bc = Vec::new();
            compile_expr(body, &mut bc);
            out.push(BytecodeOp::Quantifier {
                kind: kind.clone(),
                var: var.clone(),
                domain_code: dc,
                body_code: bc,
            });
        }
    }
}

fn compile_action(act: &LirAction) -> CompiledAction {
    match act {
        LirAction::ReturnExpr(e) => {
            let mut c = Vec::new();
            compile_expr(e, &mut c);
            CompiledAction::ReturnExpr(c)
        }
        LirAction::AssignState(ups) => {
            let mut c_ups = Vec::new();
            for (v, ue) in ups {
                let mut c = Vec::new();
                compile_expr(ue, &mut c);
                c_ups.push((v.clone(), c));
            }
            CompiledAction::AssignState(c_ups)
        }
        LirAction::Nop => CompiledAction::Nop,
        LirAction::TrapAbort => CompiledAction::TrapAbort,
    }
}

impl fmt::Display for BytecodeProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "=== BIL Bytecode VM Image ({} functions, {} globals, {} instructions, {} ghost items erased) ===",
            self.functions.len(),
            self.globals.len(),
            self.total_instructions(),
            self.erased_ghost_count
        )?;
        for func in self.functions.values() {
            writeln!(f, "  .fn {}({}):", func.name, func.params.join(", "))?;
            for (idx, op) in func.code.iter().enumerate() {
                writeln!(f, "    {:04}: {:?}", idx, op)?;
            }
        }
        for (gname, code) in &self.globals {
            writeln!(f, "  .global {}:", gname)?;
            for (idx, op) in code.iter().enumerate() {
                writeln!(f, "    {:04}: {:?}", idx, op)?;
            }
        }
        Ok(())
    }
}

/// Stack/Register Virtual Machine executing Ghost-Erased `BytecodeProgram`
pub struct BytecodeVm {
    pub ontology: OntologyRegistry,
    pub prog: BytecodeProgram,
    pub globals: BTreeMap<String, Value>,
    pub concept_store: BTreeMap<String, Vec<Value>>,
    pub rng_state: u64,
}

impl BytecodeVm {
    pub fn new(ontology: OntologyRegistry, prog: BytecodeProgram, seed: u64) -> Self {
        let mut globals = BTreeMap::new();
        for (vname, arity) in &prog.adt_variants {
            if *arity == 0 {
                globals.insert(
                    vname.clone(),
                    Value::AdtVariant {
                        variant: vname.clone(),
                        fields: vec![],
                    },
                );
            }
        }
        Self {
            ontology,
            prog,
            globals,
            concept_store: BTreeMap::new(),
            rng_state: if seed == 0 { 0x9E3779B97F4A7C15 } else { seed },
        }
    }

    fn next_rand_index(&mut self, len: usize) -> usize {
        if len <= 1 {
            return 0;
        }
        let mut x = self.rng_state;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.rng_state = x;
        let r = x.wrapping_mul(0x2545F4914F6CDD1D);
        (r as usize) % len
    }

    fn register_instance(&mut self, val: &Value) {
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

    pub fn execute(&mut self) -> Result<Vec<(String, Value)>, String> {
        let mut results = Vec::new();
        let globals_code = self.prog.globals.clone();
        for (gname, code) in globals_code {
            let mut env = BTreeMap::new();
            let val = self.exec_code(&code, &mut env)?;
            self.register_instance(&val);
            self.globals.insert(gname.clone(), val.clone());
            results.push((gname, val));
        }
        Ok(results)
    }

    pub fn exec_code(
        &mut self,
        code: &[BytecodeOp],
        env: &mut BTreeMap<String, Value>,
    ) -> Result<Value, String> {
        let mut stack: Vec<Value> = Vec::new();
        let mut saved_vars: Vec<(String, Option<Value>)> = Vec::new();

        for op in code {
            match op {
                BytecodeOp::PushInt(v) => stack.push(Value::Int(*v)),
                BytecodeOp::PushFloat(v) => stack.push(Value::Float(*v)),
                BytecodeOp::PushBool(v) => stack.push(Value::Bool(*v)),
                BytecodeOp::PushStr(s) => stack.push(Value::Str(s.clone())),
                BytecodeOp::LoadVar(name) => {
                    if let Some(v) = env.get(name) {
                        stack.push(v.clone());
                    } else if let Some(v) = self.globals.get(name) {
                        stack.push(v.clone());
                    } else if self.ontology.concepts.contains_key(name) {
                        let mut instances = Vec::new();
                        let concepts: Vec<String> =
                            self.ontology.concepts.keys().cloned().collect();
                        for c in concepts {
                            if self.ontology.is_subconcept(&c, name) {
                                if let Some(list) = self.concept_store.get(&c) {
                                    for item in list {
                                        if !instances.contains(item) {
                                            instances.push(item.clone());
                                        }
                                    }
                                }
                            }
                        }
                        stack.push(Value::List(Rc::new(instances)));
                    } else {
                        return Err(format!("VM unbound variable '{}'", name));
                    }
                }
                BytecodeOp::StoreVar(name) => {
                    let val = stack.pop().ok_or("VM stack underflow on StoreVar")?;
                    let prev = env.insert(name.clone(), val);
                    saved_vars.push((name.clone(), prev));
                }
                BytecodeOp::PopVar(name) => {
                    if let Some(( popped_name, prev)) = saved_vars.pop() {
                        if &popped_name == name {
                            if let Some(p) = prev {
                                env.insert(name.clone(), p);
                            } else {
                                env.remove(name);
                            }
                        }
                    }
                }
                BytecodeOp::Unary(uop) => {
                    let v = stack.pop().ok_or("VM stack underflow on Unary")?;
                    let res = match (uop, v) {
                        (UnaryOp::Not, Value::Bool(b)) => Value::Bool(!b),
                        (UnaryOp::Neg, Value::Int(i)) => Value::Int(crate::semantics::int_neg(i)?),
                        (UnaryOp::Neg, Value::Float(f)) => Value::Float(-f),
                        _ => return Err("VM invalid unary operand".into()),
                    };
                    stack.push(res);
                }
                BytecodeOp::Binary(bop) => {
                    let r = stack.pop().ok_or("VM stack underflow on Binary rhs")?;
                    let l = stack.pop().ok_or("VM stack underflow on Binary lhs")?;
                    let res = eval_vm_binop(*bop, l, r)?;
                    stack.push(res);
                }
                BytecodeOp::MakeList(n) => {
                    let start = stack.len().saturating_sub(*n);
                    let items: Vec<Value> = stack.drain(start..).collect();
                    stack.push(Value::List(Rc::new(items)));
                }
                BytecodeOp::MakeStruct { concept, fields } => {
                    let start = stack.len().saturating_sub(fields.len());
                    let vals: Vec<Value> = stack.drain(start..).collect();
                    let mut map = BTreeMap::new();
                    for (k, v) in fields.iter().zip(vals.into_iter()) {
                        map.insert(k.clone(), v);
                    }
                    let inst = Value::ConceptInstance {
                        concept: concept.clone(),
                        fields: map,
                    };
                    self.register_instance(&inst);
                    stack.push(inst);
                }
                BytecodeOp::UpdateStruct { fields } => {
                    let start = stack.len().saturating_sub(fields.len());
                    let vals: Vec<Value> = stack.drain(start..).collect();
                    let base = stack.pop().ok_or("VM stack underflow on UpdateStruct")?;
                    if let Value::ConceptInstance {
                        concept,
                        fields: mut map,
                    } = base
                    {
                        for (k, v) in fields.iter().zip(vals.into_iter()) {
                            map.insert(k.clone(), v);
                        }
                        let inst = Value::ConceptInstance {
                            concept,
                            fields: map,
                        };
                        self.register_instance(&inst);
                        stack.push(inst);
                    } else {
                        return Err("UpdateStruct expects ConceptInstance".into());
                    }
                }
                BytecodeOp::GetField(field) => {
                    let base = stack.pop().ok_or("VM stack underflow on GetField")?;
                    if let Value::ConceptInstance { fields, .. } = base {
                        let v = fields
                            .get(field)
                            .cloned()
                            .ok_or_else(|| format!("Unknown field '{}'", field))?;
                        stack.push(v);
                    } else {
                        return Err("GetField expects ConceptInstance".into());
                    }
                }
                BytecodeOp::Call { func, argc } => {
                    let start = stack.len().saturating_sub(*argc);
                    let args: Vec<Value> = stack.drain(start..).collect();
                    let res = self.exec_call(func, args)?;
                    stack.push(res);
                }
                BytecodeOp::PipeStage { stage, arg } => {
                    let input = stack.pop().ok_or("VM stack underflow on PipeStage")?;
                    let res = self.exec_pipe_stage(stage, input, arg.as_ref(), env)?;
                    stack.push(res);
                }
                BytecodeOp::GuardedSelect { branches } => {
                    let mut enabled = Vec::new();
                    for (idx, (gcode, _)) in branches.iter().enumerate() {
                        let gval = self.exec_code(gcode, env)?;
                        if gval == Value::Bool(true) {
                            enabled.push(idx);
                        }
                    }
                    if enabled.is_empty() {
                        return Err("VM Guarded 'if ... fi' abort: no guard enabled (¬BB)".into());
                    }
                    let chosen = enabled[self.next_rand_index(enabled.len())];
                    match &branches[chosen].1 {
                        CompiledAction::ReturnExpr(ecode) => {
                            stack.push(self.exec_code(ecode, env)?);
                        }
                        CompiledAction::AssignState(ups) => {
                            let mut next_vals = Vec::new();
                            for (v, ucode) in ups {
                                next_vals.push((v.clone(), self.exec_code(ucode, env)?));
                            }
                            for (v, nv) in next_vals {
                                env.insert(v, nv);
                            }
                            stack.push(Value::Unit);
                        }
                        CompiledAction::Nop => stack.push(Value::Unit),
                        CompiledAction::TrapAbort => return Err("VM Explicit 'abort'".into()),
                    }
                }
                BytecodeOp::GuardedLoop {
                    inits,
                    branches,
                    then_code,
                } => {
                    let mut loop_env = env.clone();
                    for (vname, ic) in inits {
                        let iv = self.exec_code(ic, &mut loop_env)?;
                        loop_env.insert(vname.clone(), iv);
                    }
                    let first_var = inits[0].0.clone();
                    let mut steps = 0usize;
                    loop {
                        if steps > 100_000 {
                            return Err("VM Guarded loop exceeded 100,000 steps".into());
                        }
                        let mut enabled = Vec::new();
                        for (idx, (gc, _)) in branches.iter().enumerate() {
                            if self.exec_code(gc, &mut loop_env)? == Value::Bool(true) {
                                enabled.push(idx);
                            }
                        }
                        if enabled.is_empty() {
                            break;
                        }
                        let chosen = enabled[self.next_rand_index(enabled.len())];
                        match &branches[chosen].1 {
                            CompiledAction::AssignState(ups) => {
                                let mut evaled = Vec::new();
                                for (v, uc) in ups {
                                    evaled.push((v.clone(), self.exec_code(uc, &mut loop_env)?));
                                }
                                for (v, nv) in evaled {
                                    loop_env.insert(v, nv);
                                }
                            }
                            CompiledAction::ReturnExpr(ec) => {
                                let nv = self.exec_code(ec, &mut loop_env)?;
                                loop_env.insert(first_var.clone(), nv);
                            }
                            CompiledAction::Nop => {}
                            CompiledAction::TrapAbort => return Err("VM Loop 'abort'".into()),
                        }
                        steps += 1;
                    }
                    let res = self.exec_code(then_code, &mut loop_env)?;
                    stack.push(res);
                }
                BytecodeOp::Match { arms } => {
                    let scrut = stack.pop().ok_or("VM stack underflow on Match")?;
                    let mut matched = None;
                    for (pat, bcode) in arms {
                        let mut arm_env = env.clone();
                        if match_pattern(pat, &scrut, &mut arm_env) {
                            matched = Some(self.exec_code(bcode, &mut arm_env)?);
                            break;
                        }
                    }
                    let res = matched.ok_or("VM non-exhaustive match")?;
                    stack.push(res);
                }
                BytecodeOp::Quantifier {
                    kind,
                    var,
                    domain_code,
                    body_code,
                } => {
                    let dom = self.exec_code(domain_code, env)?;
                    let items = match dom {
                        Value::List(l) => l,
                        _ => return Err("VM quantifier domain must be List".into()),
                    };
                    match kind {
                        QuantifierKind::Forall => {
                            let mut ok = true;
                            for it in items.iter() {
                                let mut inner = env.clone();
                                inner.insert(var.clone(), it.clone());
                                if self.exec_code(body_code, &mut inner)? != Value::Bool(true) {
                                    ok = false;
                                    break;
                                }
                            }
                            stack.push(Value::Bool(ok));
                        }
                        QuantifierKind::Exists => {
                            let mut ok = false;
                            for it in items.iter() {
                                let mut inner = env.clone();
                                inner.insert(var.clone(), it.clone());
                                if self.exec_code(body_code, &mut inner)? == Value::Bool(true) {
                                    ok = true;
                                    break;
                                }
                            }
                            stack.push(Value::Bool(ok));
                        }
                        QuantifierKind::Choose => {
                            let mut candidates = Vec::new();
                            for it in items.iter() {
                                let mut inner = env.clone();
                                inner.insert(var.clone(), it.clone());
                                if self.exec_code(body_code, &mut inner)? == Value::Bool(true) {
                                    candidates.push(it.clone());
                                }
                            }
                            if candidates.is_empty() {
                                return Err(format!("VM choose {} has empty domain", var));
                            }
                            let idx = self.next_rand_index(candidates.len());
                            stack.push(candidates[idx].clone());
                        }
                    }
                }
                BytecodeOp::Return => {
                    return stack.pop().ok_or_else(|| "VM empty stack on Return".into());
                }
            }
        }

        stack.pop().ok_or_else(|| "VM empty stack at end of block".into())
    }

    fn exec_call(&mut self, func: &str, args: Vec<Value>) -> Result<Value, String> {
        match func {
            "min" if args.len() == 2 => match (&args[0], &args[1]) {
                (Value::Int(a), Value::Int(b)) => return Ok(Value::Int(*a.min(b))),
                _ => return Err("min expects Int".into()),
            },
            "max" if args.len() == 2 => match (&args[0], &args[1]) {
                (Value::Int(a), Value::Int(b)) => return Ok(Value::Int(*a.max(b))),
                _ => return Err("max expects Int".into()),
            },
            "abs" if args.len() == 1 => match &args[0] {
                Value::Int(a) => return Ok(Value::Int(crate::semantics::int_abs(*a)?)),
                _ => return Err("abs expects Int".into()),
            },
            "count" if args.len() == 1 => match &args[0] {
                Value::List(l) => return Ok(Value::Int(l.len() as i64)),
                _ => return Err("count expects List".into()),
            },
            "sum" if args.len() == 1 => match &args[0] {
                Value::List(l) => {
                    let mut s = 0i64;
                    for it in l.iter() {
                        if let Value::Int(v) = it {
                            s = crate::semantics::int_add(s, *v)?;
                        }
                    }
                    return Ok(Value::Int(s));
                }
                _ => return Err("sum expects List<Int>".into()),
            },
            _ => {}
        }

        if self.prog.adt_variants.contains_key(func) {
            return Ok(Value::AdtVariant {
                variant: func.to_string(),
                fields: args,
            });
        }

        let cfn = self
            .prog
            .functions
            .get(func)
            .cloned()
            .ok_or_else(|| format!("VM unknown function '{}'", func))?;
        let mut fn_env = BTreeMap::new();
        for (p, val) in cfn.params.iter().zip(args.into_iter()) {
            fn_env.insert(p.clone(), val);
        }
        self.exec_code(&cfn.code, &mut fn_env)
    }

    fn exec_pipe_stage(
        &mut self,
        stage: &str,
        input: Value,
        arg: Option<&LirExpr>,
        env: &mut BTreeMap<String, Value>,
    ) -> Result<Value, String> {
        match stage {
            "count" => match input {
                Value::List(l) => Ok(Value::Int(l.len() as i64)),
                _ => Err("Pipe 'count' expects List".into()),
            },
            "sum" => match input {
                Value::List(l) => {
                    let mut s = 0i64;
                    for it in l.iter() {
                        if let Value::Int(v) = it {
                            s = crate::semantics::int_add(s, *v)?;
                        }
                    }
                    Ok(Value::Int(s))
                }
                _ => Err("Pipe 'sum' expects List<Int>".into()),
            },
            "first" => match input {
                Value::List(l) => l.first().cloned().ok_or_else(|| "Empty list in first".into()),
                _ => Err("Pipe 'first' expects List".into()),
            },
            "last" => match input {
                Value::List(l) => l.last().cloned().ok_or_else(|| "Empty list in last".into()),
                _ => Err("Pipe 'last' expects List".into()),
            },
            "filter" | "where" => {
                let pred = arg.ok_or("filter requires predicate")?;
                let mut pred_code = Vec::new();
                compile_expr(pred, &mut pred_code);
                let items = match input {
                    Value::List(l) => l,
                    _ => return Err("filter expects List".into()),
                };
                let mut out = Vec::new();
                for it in items.iter() {
                    let mut sub = env.clone();
                    sub.insert("_".into(), it.clone());
                    if self.exec_code(&pred_code, &mut sub)? == Value::Bool(true) {
                        out.push(it.clone());
                    }
                }
                Ok(Value::List(Rc::new(out)))
            }
            "map" | "select" => {
                let mapper = arg.ok_or("map requires expression")?;
                let mut map_code = Vec::new();
                compile_expr(mapper, &mut map_code);
                let items = match input {
                    Value::List(l) => l,
                    _ => return Err("map expects List".into()),
                };
                let mut out = Vec::new();
                for it in items.iter() {
                    let mut sub = env.clone();
                    sub.insert("_".into(), it.clone());
                    let mv = self.exec_code(&map_code, &mut sub)?;
                    self.register_instance(&mv);
                    out.push(mv);
                }
                Ok(Value::List(Rc::new(out)))
            }
            "sort_by" => {
                let key_expr = arg.ok_or("sort_by requires key expression")?;
                let mut key_code = Vec::new();
                compile_expr(key_expr, &mut key_code);
                let items = match input {
                    Value::List(l) => l,
                    _ => return Err("sort_by expects List".into()),
                };
                let mut keyed = Vec::new();
                for it in items.iter() {
                    let mut sub = env.clone();
                    sub.insert("_".into(), it.clone());
                    let k = self.exec_code(&key_code, &mut sub)?;
                    keyed.push((k, it.clone()));
                }
                keyed.sort_by(|(ka, _), (kb, _)| match (ka, kb) {
                    (Value::Int(a), Value::Int(b)) => a.cmp(b),
                    (Value::Str(a), Value::Str(b)) => a.cmp(b),
                    _ => std::cmp::Ordering::Equal,
                });
                let sorted: Vec<Value> = keyed.into_iter().map(|(_, v)| v).collect();
                Ok(Value::List(Rc::new(sorted)))
            }
            "all" => {
                let pred = arg.ok_or("all requires predicate")?;
                let mut pred_code = Vec::new();
                compile_expr(pred, &mut pred_code);
                let items = match input {
                    Value::List(l) => l,
                    _ => return Err("all expects List".into()),
                };
                for it in items.iter() {
                    let mut sub = env.clone();
                    sub.insert("_".into(), it.clone());
                    if self.exec_code(&pred_code, &mut sub)? != Value::Bool(true) {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            "any" => {
                let pred = arg.ok_or("any requires predicate")?;
                let mut pred_code = Vec::new();
                compile_expr(pred, &mut pred_code);
                let items = match input {
                    Value::List(l) => l,
                    _ => return Err("any expects List".into()),
                };
                for it in items.iter() {
                    let mut sub = env.clone();
                    sub.insert("_".into(), it.clone());
                    if self.exec_code(&pred_code, &mut sub)? == Value::Bool(true) {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(false))
            }
            other => {
                // User function call in pipeline (supports `_` placeholder)
                if matches!(arg, Some(LirExpr::Placeholder)) {
                    self.exec_call(other, vec![input])
                } else {
                    let mut sub = env.clone();
                    sub.insert("_".into(), input.clone());
                    let mut args = vec![input];
                    if let Some(a) = arg {
                        let mut ac = Vec::new();
                        compile_expr(a, &mut ac);
                        args.push(self.exec_code(&ac, &mut sub)?);
                    }
                    self.exec_call(other, args)
                }
            }
        }
    }
}

fn eval_vm_binop(op: BinOp, l: Value, r: Value) -> Result<Value, String> {
    match op {
        BinOp::Implies => match (l, r) {
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(!a || b)),
            _ => Err("=> expects Bool".into()),
        },
        BinOp::Iff => match (l, r) {
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
            _ => Err("<=> expects Bool".into()),
        },
        BinOp::And => match (l, r) {
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a && b)),
            _ => Err("&& expects Bool".into()),
        },
        BinOp::Or => match (l, r) {
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a || b)),
            _ => Err("|| expects Bool".into()),
        },
        BinOp::Eq => Ok(Value::Bool(l == r)),
        BinOp::Neq => Ok(Value::Bool(l != r)),
        BinOp::Lt => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
            _ => Err("< expects numeric".into()),
        },
        BinOp::Le => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
            _ => Err("<= expects numeric".into()),
        },
        BinOp::Gt => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
            _ => Err("> expects numeric".into()),
        },
        BinOp::Ge => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
            _ => Err(">= expects numeric".into()),
        },
        BinOp::In => match (l, r) {
            (elem, Value::List(list)) => Ok(Value::Bool(list.contains(&elem))),
            _ => Err("in expects List".into()),
        },
        BinOp::Range => match (l, r) {
            (Value::Int(a), Value::Int(b)) => {
                Ok(Value::List(Rc::new((a..b).map(Value::Int).collect())))
            }
            _ => Err(".. expects Int".into()),
        },
        BinOp::RangeInc => match (l, r) {
            (Value::Int(a), Value::Int(b)) => {
                Ok(Value::List(Rc::new((a..=b).map(Value::Int).collect())))
            }
            _ => Err("..= expects Int".into()),
        },
        BinOp::Add => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(crate::semantics::int_add(a, b)?)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            (Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{}{}", a, b))),
            _ => Err("+ expects matching numeric or String".into()),
        },
        BinOp::Sub => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(crate::semantics::int_sub(a, b)?)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
            _ => Err("- expects numeric".into()),
        },
        BinOp::Mul => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(crate::semantics::int_mul(a, b)?)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
            _ => Err("* expects numeric".into()),
        },
        BinOp::Div => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(crate::semantics::int_div(a, b)?)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
            _ => Err("/ expects numeric".into()),
        },
        BinOp::Mod => match (l, r) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(crate::semantics::int_mod(a, b)?)),
            _ => Err("% expects Int".into()),
        },
        BinOp::Pipe => Err("Raw Pipe in VM binary op".into()),
    }
}

fn match_pattern(pat: &Pattern, val: &Value, env: &mut BTreeMap<String, Value>) -> bool {
    match (pat, val) {
        (Pattern::Wildcard, _) => true,
        (Pattern::Var(v), _) => {
            env.insert(v.clone(), val.clone());
            true
        }
        (Pattern::Int(a), Value::Int(b)) => a == b,
        (Pattern::Bool(a), Value::Bool(b)) => a == b,
        (Pattern::Str(a), Value::Str(b)) => a == b,
        (Pattern::Variant(vname, bindings), Value::AdtVariant { variant, fields }) => {
            if vname != variant || bindings.len() != fields.len() {
                return false;
            }
            for (b, fval) in bindings.iter().zip(fields.iter()) {
                if b != "_" {
                    env.insert(b.clone(), fval.clone());
                }
            }
            true
        }
        _ => false,
    }
}
