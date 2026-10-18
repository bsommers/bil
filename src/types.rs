use crate::ast::*;
use crate::lexer::Span;
use crate::ontology::OntologyRegistry;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Float,
    Bool,
    Str,
    Unit,
    Var(usize),
    Concept(String),
    Adt(String),
    List(Box<Type>),
    Map(Box<Type>, Box<Type>),
    Fn(Vec<Type>, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Float => write!(f, "Float"),
            Type::Bool => write!(f, "Bool"),
            Type::Str => write!(f, "String"),
            Type::Unit => write!(f, "Unit"),
            Type::Var(id) => write!(f, "'t{}", id),
            Type::Concept(c) => write!(f, "{}", c),
            Type::Adt(a) => write!(f, "{}", a),
            Type::List(inner) => write!(f, "List<{}>", inner),
            Type::Map(k, v) => write!(f, "Map<{}, {}>", k, v),
            Type::Fn(args, ret) => {
                let s: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "({}) -> {}", s.join(", "), ret)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[TypeError at {}] {}", self.span, self.message)
    }
}

#[derive(Debug, Clone)]
pub struct AdtInfo {
    pub name: String,
    pub variants: BTreeMap<String, Vec<Type>>,
}

#[derive(Debug, Clone)]
pub struct TypeEnv {
    pub ontology: OntologyRegistry,
    pub adts: BTreeMap<String, AdtInfo>,
    pub variant_to_adt: BTreeMap<String, (String, Vec<Type>)>,
    pub specs: BTreeMap<String, (Vec<Type>, Type)>,
    pub bindings: BTreeMap<String, Type>,
    next_var: usize,
    subst: BTreeMap<usize, Type>,
}

impl TypeEnv {
    pub fn new(ontology: OntologyRegistry) -> Self {
        let mut env = Self {
            ontology,
            adts: BTreeMap::new(),
            variant_to_adt: BTreeMap::new(),
            specs: BTreeMap::new(),
            bindings: BTreeMap::new(),
            next_var: 0,
            subst: BTreeMap::new(),
        };
        // Register standard math & query builtins from centralized BuiltinFn registry
        for b in crate::builtins::BuiltinFn::ALL {
            if let Some((params, ret)) = b.monomorphic_signature() {
                env.bindings
                    .insert(b.as_str().into(), Type::Fn(params, Box::new(ret)));
            }
        }
        env
    }

    pub fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(sub) = self.subst.get(id) {
                    self.apply(sub)
                } else {
                    Type::Var(*id)
                }
            }
            Type::List(inner) => Type::List(Box::new(self.apply(inner))),
            Type::Map(k, v) => Type::Map(Box::new(self.apply(k)), Box::new(self.apply(v))),
            Type::Fn(args, ret) => Type::Fn(
                args.iter().map(|a| self.apply(a)).collect(),
                Box::new(self.apply(ret)),
            ),
            other => other.clone(),
        }
    }

    fn occurs(&self, id: usize, ty: &Type) -> bool {
        match self.apply(ty) {
            Type::Var(v) => v == id,
            Type::List(inner) => self.occurs(id, &inner),
            Type::Map(k, v) => self.occurs(id, &k) || self.occurs(id, &v),
            Type::Fn(args, ret) => {
                args.iter().any(|a| self.occurs(id, a)) || self.occurs(id, &ret)
            }
            _ => false,
        }
    }

    /// Unifies `actual` with `expected`, respecting OntoLogic subtyping (`sub <: sup`)
    pub fn unify(&mut self, actual: &Type, expected: &Type, span: Span) -> Result<Type, TypeError> {
        let a = self.apply(actual);
        let e = self.apply(expected);

        match (&a, &e) {
            (x, y) if x == y => Ok(x.clone()),
            (Type::Var(id), other) => {
                if self.occurs(*id, other) {
                    return Err(TypeError {
                        message: format!("Infinite type detected unifying 't{} with {}", id, other),
                        span,
                    });
                }
                self.subst.insert(*id, other.clone());
                Ok(other.clone())
            }
            (other, Type::Var(id)) => {
                if self.occurs(*id, other) {
                    return Err(TypeError {
                        message: format!("Infinite type detected unifying {} with 't{}", other, id),
                        span,
                    });
                }
                self.subst.insert(*id, other.clone());
                Ok(other.clone())
            }
            (Type::Concept(sub), Type::Concept(sup)) => {
                if self.ontology.is_subconcept(sub, sup) {
                    Ok(Type::Concept(sup.clone()))
                } else {
                    Err(TypeError {
                        message: format!(
                            "OntoLogic concept '{}' is not a subconcept of '{}'",
                            sub, sup
                        ),
                        span,
                    })
                }
            }
            (Type::List(ia), Type::List(ie)) => {
                let u = self.unify(ia, ie, span)?;
                Ok(Type::List(Box::new(u)))
            }
            (Type::Map(ka, va), Type::Map(ke, ve)) => {
                let uk = self.unify(ka, ke, span)?;
                let uv = self.unify(va, ve, span)?;
                Ok(Type::Map(Box::new(uk), Box::new(uv)))
            }
            (Type::Fn(aa, ra), Type::Fn(ae, re)) if aa.len() == ae.len() => {
                let mut uargs = Vec::new();
                for (x, y) in aa.iter().zip(ae.iter()) {
                    uargs.push(self.unify(y, x, span)?);
                }
                let uret = self.unify(ra, re, span)?;
                Ok(Type::Fn(uargs, Box::new(uret)))
            }
            _ => Err(TypeError {
                message: format!("Type mismatch: expected {}, found {}", e, a),
                span,
            }),
        }
    }

    /// Computes the least upper bound (join) of two types in symmetric contexts (`List`, `IfFi`, `Match`, `==`/`!=`).
    pub fn join_types(&mut self, t1: &Type, t2: &Type, span: Span) -> Result<Type, TypeError> {
        let a = self.apply(t1);
        let b = self.apply(t2);
        match (&a, &b) {
            (Type::Concept(c1), Type::Concept(c2)) => {
                if let Some(anc) = self.ontology.common_ancestor(c1, c2) {
                    Ok(Type::Concept(anc))
                } else {
                    Err(TypeError {
                        message: format!(
                            "OntoLogic concepts '{}' and '{}' have no common ancestor",
                            c1, c2
                        ),
                        span,
                    })
                }
            }
            (Type::List(ia), Type::List(ib)) => {
                let j = self.join_types(ia, ib, span)?;
                Ok(Type::List(Box::new(j)))
            }
            _ => self.unify(&a, &b, span),
        }
    }

    pub fn resolve_type_expr(&self, texpr: &TypeExpr, span: Span) -> Result<Type, TypeError> {
        match texpr {
            TypeExpr::Named(n) => match n.as_str() {
                "Int" | "Integer" => Ok(Type::Int),
                "Float" | "Double" => Ok(Type::Float),
                "Bool" | "Boolean" => Ok(Type::Bool),
                "String" | "Str" => Ok(Type::Str),
                "Unit" => Ok(Type::Unit),
                other => {
                    if self.ontology.concepts.contains_key(other) {
                        Ok(Type::Concept(other.to_string()))
                    } else if self.adts.contains_key(other) {
                        Ok(Type::Adt(other.to_string()))
                    } else {
                        Err(TypeError {
                            message: format!("Unknown type or concept '{}'", other),
                            span,
                        })
                    }
                }
            },
            TypeExpr::List(inner) => Ok(Type::List(Box::new(self.resolve_type_expr(inner, span)?))),
            TypeExpr::Map(k, v) => Ok(Type::Map(
                Box::new(self.resolve_type_expr(k, span)?),
                Box::new(self.resolve_type_expr(v, span)?),
            )),
            TypeExpr::Fn(args, ret) => {
                let mut rargs = Vec::new();
                for a in args {
                    rargs.push(self.resolve_type_expr(a, span)?);
                }
                Ok(Type::Fn(
                    rargs,
                    Box::new(self.resolve_type_expr(ret, span)?),
                ))
            }
        }
    }

    pub fn check_program(&mut self, program: &Program) -> Result<(), Vec<TypeError>> {
        let mut errors = Vec::new();

        // Pass 1: Register ADTs
        for item in &program.items {
            if let Item::TypeDecl(adt) = item {
                self.adts.insert(
                    adt.name.clone(),
                    AdtInfo {
                        name: adt.name.clone(),
                        variants: BTreeMap::new(),
                    },
                );
            }
        }
        for item in &program.items {
            if let Item::TypeDecl(adt) = item {
                let mut vmap = BTreeMap::new();
                for v in &adt.variants {
                    let mut ptypes = Vec::new();
                    for p in &v.payload {
                        match self.resolve_type_expr(p, adt.span) {
                            Ok(t) => ptypes.push(t),
                            Err(e) => errors.push(e),
                        }
                    }
                    vmap.insert(v.name.clone(), ptypes.clone());
                    self.variant_to_adt
                        .insert(v.name.clone(), (adt.name.clone(), ptypes.clone()));
                    if ptypes.is_empty() {
                        self.bindings
                            .insert(v.name.clone(), Type::Adt(adt.name.clone()));
                    } else {
                        self.bindings.insert(
                            v.name.clone(),
                            Type::Fn(ptypes, Box::new(Type::Adt(adt.name.clone()))),
                        );
                    }
                }
                if let Some(info) = self.adts.get_mut(&adt.name) {
                    info.variants = vmap;
                }
            }
        }

        // Pass 2: Register Specs and Function signatures
        for item in &program.items {
            match item {
                Item::Spec(sp) => {
                    let mut ptypes = Vec::new();
                    for p in &sp.params {
                        match self.resolve_type_expr(&p.ty, sp.span) {
                            Ok(t) => ptypes.push(t),
                            Err(e) => errors.push(e),
                        }
                    }
                    if let Ok(ret) = self.resolve_type_expr(&sp.ret_ty, sp.span) {
                        self.specs.insert(sp.name.clone(), (ptypes, ret));
                    }
                }
                Item::FnDecl(f) => {
                    let mut ptypes = Vec::new();
                    for p in &f.params {
                        match self.resolve_type_expr(&p.ty, f.span) {
                            Ok(t) => ptypes.push(t),
                            Err(e) => errors.push(e),
                        }
                    }
                    match self.resolve_type_expr(&f.ret_ty, f.span) {
                        Ok(ret) => {
                            self.bindings
                                .insert(f.name.clone(), Type::Fn(ptypes, Box::new(ret)));
                        }
                        Err(e) => errors.push(e),
                    }
                }
                _ => {}
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        // Pass 3: Check all declarations & bodies
        for item in &program.items {
            if let Err(e) = self.check_item(item) {
                errors.push(e);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn check_item(&mut self, item: &Item) -> Result<(), TypeError> {
        match item {
            Item::Concept(_) | Item::TypeDecl(_) => Ok(()),
            Item::Axiom(ax) => {
                let mut local = self. bindings.clone();
                let ty = self.infer_expr(&ax.formula, &mut local, ax.span)?;
                self.unify(&ty, &Type::Bool, ax.span)?;
                Ok(())
            }
            Item::Spec(sp) => {
                let mut local = self.bindings.clone();
                for p in &sp.params {
                    let pt = self.resolve_type_expr(&p.ty, sp.span)?;
                    local.insert(p.name.clone(), pt);
                }
                let ret_ty = self.resolve_type_expr(&sp.ret_ty, sp.span)?;
                if let Some(req) = &sp.requires {
                    let rt = self.infer_expr(req, &mut local, sp.span)?;
                    self.unify(&rt, &Type::Bool, sp.span)?;
                }
                if let Some(ens) = &sp.ensures {
                    local.insert("result".into(), ret_ty);
                    let et = self.infer_expr(ens, &mut local, sp.span)?;
                    self.unify(&et, &Type::Bool, sp.span)?;
                }
                Ok(())
            }
            Item::Proof(pr) => {
                let mut local = self.bindings.clone();
                for p in &pr.params {
                    let pt = self.resolve_type_expr(&p.ty, pr.span)?;
                    local.insert(p.name.clone(), pt);
                }
                if let Some(req) = &pr.requires {
                    let rt = self.infer_expr(req, &mut local, pr.span)?;
                    self.unify(&rt, &Type::Bool, pr.span)?;
                }
                let et = self.infer_expr(&pr.ensures, &mut local, pr.span)?;
                self.unify(&et, &Type::Bool, pr.span)?;
                if let Some(b) = &pr.body {
                    let bt = self.infer_expr(b, &mut local, pr.span)?;
                    self.unify(&bt, &Type::Bool, pr.span)?;
                }
                Ok(())
            }
            Item::FnDecl(f) => {
                let mut local = self.bindings.clone();
                let mut param_types = Vec::new();
                for p in &f.params {
                    let pt = self.resolve_type_expr(&p.ty, f.span)?;
                    param_types.push(pt.clone());
                    local.insert(p.name.clone(), pt);
                }
                let ret_ty = self.resolve_type_expr(&f.ret_ty, f.span)?;

                if let Some(spec_name) = &f.refines {
                    let (sp_params, sp_ret) =
                        self.specs.get(spec_name).cloned().ok_or_else(|| TypeError {
                            message: format!(
                                "Function '{}' refines unknown spec '{}'",
                                f.name, spec_name
                            ),
                            span: f.span,
                        })?;
                    if sp_params.len() != param_types.len() {
                        return Err(TypeError {
                            message: format!(
                                "Refinement '{}' parameter count mismatch with spec '{}'",
                                f.name, spec_name
                            ),
                            span: f.span,
                        });
                    }
                    for (pt, spt) in param_types.iter().zip(sp_params.iter()) {
                        self.unify(pt, spt, f.span)?;
                    }
                    self.unify(&ret_ty, &sp_ret, f.span)?;
                }

                if let Some(req) = &f.requires {
                    let rt = self.infer_expr(req, &mut local, f.span)?;
                    self.unify(&rt, &Type::Bool, f.span)?;
                }

                let body_ty = self.infer_expr(&f.body, &mut local, f.span)?;
                self.unify(&body_ty, &ret_ty, f.span)?;

                if let Some(ens) = &f.ensures {
                    local.insert("result".into(), ret_ty);
                    let et = self.infer_expr(ens, &mut local, f.span)?;
                    self.unify(&et, &Type::Bool, f.span)?;
                }
                Ok(())
            }
            Item::System(sys) => {
                let mut local = self.bindings.clone();
                for st in &sys.states {
                    let expected_ty = self.resolve_type_expr(&st.ty, sys.span)?;
                    let init_ty = self.infer_expr(&st.init, &mut local, sys.span)?;
                    self.unify(&init_ty, &expected_ty, sys.span)?;
                    local.insert(st.name.clone(), expected_ty);
                }
                for inv in &sys.invariants {
                    let it = self.infer_expr(&inv.formula, &mut local, sys.span)?;
                    self.unify(&it, &Type::Bool, sys.span)?;
                }
                for temp in &sys.temporals {
                    match &temp.formula {
                        TemporalFormula::Always(e) | TemporalFormula::Eventually(e) => {
                            let tt = self.infer_expr(e, &mut local, sys.span)?;
                            self.unify(&tt, &Type::Bool, sys.span)?;
                        }
                        TemporalFormula::LeadsTo(p, q) => {
                            let pt = self.infer_expr(p, &mut local, sys.span)?;
                            self.unify(&pt, &Type::Bool, sys.span)?;
                            let qt = self.infer_expr(q, &mut local, sys.span)?;
                            self.unify(&qt, &Type::Bool, sys.span)?;
                        }
                    }
                }
                if let Some(v) = &sys.variant {
                    let vt = self.infer_expr(v, &mut local, sys.span)?;
                    self.unify(&vt, &Type::Int, sys.span)?;
                }
                if let Some(term) = &sys.terminal {
                    let tt = self.infer_expr(term, &mut local, sys.span)?;
                    self.unify(&tt, &Type::Bool, sys.span)?;
                }
                for tr in &sys.transitions {
                    let gt = self.infer_expr(&tr.guard, &mut local, sys.span)?;
                    self.unify(&gt, &Type::Bool, sys.span)?;
                    for (var, uexpr) in &tr.updates {
                        let st_ty = local.get(var).cloned().ok_or_else(|| TypeError {
                            message: format!(
                                "Transition updates undeclared state variable '{}'",
                                var
                            ),
                            span: sys.span,
                        })?;
                        let ut = self.infer_expr(uexpr, &mut local, sys.span)?;
                        self.unify(&ut, &st_ty, sys.span)?;
                    }
                }
                Ok(())
            }
            Item::Let(l) => {
                let mut local = self.bindings.clone();
                let inferred = self.infer_expr(&l.value, &mut local, l.span)?;
                let final_ty = if let Some(ann) = &l.ty {
                    let expected = self.resolve_type_expr(ann, l.span)?;
                    self.unify(&inferred, &expected, l.span)?
                } else {
                    self.apply(&inferred)
                };
                self.bindings.insert(l.name.clone(), final_ty);
                Ok(())
            }
            Item::Assert(a) => {
                let mut local = self.bindings.clone();
                let ty = self.infer_expr(&a.formula, &mut local, a.span)?;
                self.unify(&ty, &Type::Bool, a.span)?;
                Ok(())
            }
        }
    }

    pub fn infer_expr(
        &mut self,
        expr: &Expr,
        local: &mut BTreeMap<String, Type>,
        span: Span,
    ) -> Result<Type, TypeError> {
        match expr {
            Expr::Int(_) => Ok(Type::Int),
            Expr::Float(_) => Ok(Type::Float),
            Expr::Bool(_) => Ok(Type::Bool),
            Expr::Str(_) => Ok(Type::Str),
            Expr::Placeholder => {
                if let Some(p_ty) = local.get("_") {
                    Ok(p_ty.clone())
                } else {
                    Ok(self.fresh_var())
                }
            }
            Expr::Var(name) => {
                if let Some(ty) = local.get(name) {
                    Ok(ty.clone())
                } else if self.ontology.concepts.contains_key(name) {
                    // Concept name used as a domain in `forall x in Concept`
                    Ok(Type::List(Box::new(Type::Concept(name.clone()))))
                } else {
                    Err(TypeError {
                        message: format!("Unbound variable or identifier '{}'", name),
                        span,
                    })
                }
            }
            Expr::Unary { op, expr: inner } => {
                let t = self.infer_expr(inner, local, span)?;
                match op {
                    UnaryOp::Not => self.unify(&t, &Type::Bool, span),
                    UnaryOp::Neg => {
                        let applied = self.apply(&t);
                        if applied == Type::Float {
                            Ok(Type::Float)
                        } else {
                            self.unify(&t, &Type::Int, span)
                        }
                    }
                }
            }
            Expr::Binary { op, left, right } => match op {
                BinOp::Pipe => {
                    let left_ty = self.infer_expr(left, local, span)?;
                    self.infer_pipe(&left_ty, right, local, span)
                }
                BinOp::Implies | BinOp::Iff | BinOp::And | BinOp::Or => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    self.unify(&lt, &Type::Bool, span)?;
                    self.unify(&rt, &Type::Bool, span)?;
                    Ok(Type::Bool)
                }
                BinOp::Eq | BinOp::Neq => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    self.join_types(&lt, &rt, span)?;
                    Ok(Type::Bool)
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    let u = self.unify(&lt, &rt, span)?;
                    match self.apply(&u) {
                        Type::Int | Type::Float | Type::Var(_) => Ok(Type::Bool),
                        other => Err(TypeError {
                            message: format!(
                                "Comparison operator '{}' requires numeric operands (Int or Float), found {}",
                                op, other
                            ),
                            span,
                        }),
                    }
                }
                BinOp::In => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    let elem_ty = self.fresh_var();
                    self.unify(&rt, &Type::List(Box::new(elem_ty.clone())), span)?;
                    self.join_types(&lt, &elem_ty, span)?;
                    Ok(Type::Bool)
                }
                BinOp::Range | BinOp::RangeInc => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    self.unify(&lt, &Type::Int, span)?;
                    self.unify(&rt, &Type::Int, span)?;
                    Ok(Type::List(Box::new(Type::Int)))
                }
                BinOp::Mod => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    self.unify(&lt, &Type::Int, span)?;
                    self.unify(&rt, &Type::Int, span)?;
                    Ok(Type::Int)
                }
                BinOp::Sub | BinOp::Mul | BinOp::Div => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    let u = self.unify(&lt, &rt, span)?;
                    let resolved = self.apply(&u);
                    match resolved {
                        Type::Int | Type::Float | Type::Var(_) => Ok(resolved),
                        other => Err(TypeError {
                            message: format!(
                                "Arithmetic operator '{}' requires numeric operands (Int or Float), found {}",
                                op, other
                            ),
                            span,
                        }),
                    }
                }
                BinOp::Add => {
                    let lt = self.infer_expr(left, local, span)?;
                    let rt = self.infer_expr(right, local, span)?;
                    let u = self.unify(&lt, &rt, span)?;
                    let resolved = self.apply(&u);
                    match resolved {
                        Type::Int | Type::Float | Type::Str | Type::Var(_) => Ok(resolved),
                        other => Err(TypeError {
                            message: format!(
                                "Operator '+' requires numeric (Int, Float) or String operands, found {}",
                                other
                            ),
                            span,
                        }),
                    }
                }
            },
            Expr::Quantifier {
                kind,
                var,
                domain,
                body,
            } => {
                let dom_ty = self.infer_expr(domain, local, span)?;
                let elem_ty = self.fresh_var();
                self.unify(&dom_ty, &Type::List(Box::new(elem_ty.clone())), span)?;
                let resolved_elem = self.apply(&elem_ty);

                let mut inner_local = local.clone();
                inner_local.insert(var.clone(), resolved_elem.clone());
                let body_ty = self.infer_expr(body, &mut inner_local, span)?;
                self.unify(&body_ty, &Type::Bool, span)?;

                match kind {
                    QuantifierKind::Forall | QuantifierKind::Exists => Ok(Type::Bool),
                    QuantifierKind::Choose => Ok(resolved_elem),
                }
            }
            Expr::IfFi { branches } => {
                if branches.is_empty() {
                    return Err(TypeError {
                        message: "Guarded 'if ... fi' must have at least one branch".into(),
                        span,
                    });
                }
                let mut result_ty = self.fresh_var();
                for br in branches {
                    let gt = self.infer_expr(&br.guard, local, span)?;
                    self.unify(&gt, &Type::Bool, span)?;
                    match &br.body {
                        GclBody::Expr(e) => {
                            let bt = self.infer_expr(e, local, span)?;
                            result_ty = self.join_types(&bt, &result_ty, span)?;
                        }
                        GclBody::Updates(ups) => {
                            for (v, ue) in ups {
                                let vt = local.get(v).cloned().ok_or_else(|| TypeError {
                                    message: format!("Assignment to unbound variable '{}'", v),
                                    span,
                                })?;
                                let ut = self.infer_expr(ue, local, span)?;
                                self.unify(&ut, &vt, span)?;
                            }
                            result_ty = self.join_types(&Type::Unit, &result_ty, span)?;
                        }
                        GclBody::Skip | GclBody::Abort => {}
                    }
                }
                Ok(self.apply(&result_ty))
            }
            Expr::DoOd {
                inits,
                invariant,
                variant,
                branches,
                then_expr,
            } => {
                let mut loop_local = local.clone();
                for (vname, init_expr) in inits {
                    let it = self.infer_expr(init_expr, &mut loop_local, span)?;
                    loop_local.insert(vname.clone(), it);
                }
                if let Some(inv) = invariant {
                    let inv_t = self.infer_expr(inv, &mut loop_local, span)?;
                    self.unify(&inv_t, &Type::Bool, span)?;
                }
                if let Some(var_e) = variant {
                    let var_t = self.infer_expr(var_e, &mut loop_local, span)?;
                    self.unify(&var_t, &Type::Int, span)?;
                }
                let first_var_ty = loop_local
                    .get(&inits[0].0)
                    .cloned()
                    .unwrap_or(Type::Unit);
                for br in branches {
                    let gt = self.infer_expr(&br.guard, &mut loop_local, span)?;
                    self.unify(&gt, &Type::Bool, span)?;
                    match &br.body {
                        GclBody::Updates(ups) => {
                            for (v, ue) in ups {
                                let vt = loop_local.get(v).cloned().ok_or_else(|| TypeError {
                                    message: format!(
                                        "Loop branch updates unknown state variable '{}'",
                                        v
                                    ),
                                    span,
                                })?;
                                let ut = self.infer_expr(ue, &mut loop_local, span)?;
                                self.unify(&ut, &vt, span)?;
                            }
                        }
                        GclBody::Expr(e) => {
                            // Pure functional state transition: G -> next_state
                            let et = self.infer_expr(e, &mut loop_local, span)?;
                            self.unify(&et, &first_var_ty, span)?;
                        }
                        GclBody::Skip | GclBody::Abort => {}
                    }
                }
                self.infer_expr(then_expr, &mut loop_local, span)
            }
            Expr::Match { scrutinee, arms } => {
                let scr_ty = self.infer_expr(scrutinee, local, span)?;
                let scr_ty = self.apply(&scr_ty);
                let mut res_ty = self.fresh_var();
                let mut covered_variants = BTreeSet::new();
                let mut has_wildcard = false;

                for arm in arms {
                    let mut arm_local = local.clone();
                    match &arm.pattern {
                        Pattern::Wildcard => {
                            has_wildcard = true;
                        }
                        Pattern::Var(v) => {
                            has_wildcard = true;
                            arm_local.insert(v.clone(), scr_ty.clone());
                        }
                        Pattern::Int(_) => {
                            self.unify(&scr_ty, &Type::Int, span)?;
                        }
                        Pattern::Bool(_) => {
                            self.unify(&scr_ty, &Type::Bool, span)?;
                        }
                        Pattern::Str(_) => {
                            self.unify(&scr_ty, &Type::Str, span)?;
                        }
                        Pattern::Variant(vname, bindings) => {
                            let (adt_name, payload_tys) =
                                self.variant_to_adt.get(vname).cloned().ok_or_else(|| {
                                    TypeError {
                                        message: format!("Unknown ADT variant '{}'", vname),
                                        span,
                                    }
                                })?;
                            self.unify(&scr_ty, &Type::Adt(adt_name), span)?;
                            if bindings.len() != payload_tys.len() {
                                return Err(TypeError {
                                    message: format!(
                                        "Variant '{}' expects {} bindings, found {}",
                                        vname,
                                        payload_tys.len(),
                                        bindings.len()
                                    ),
                                    span,
                                });
                            }
                            covered_variants.insert(vname.clone());
                            for (b, pt) in bindings.iter().zip(payload_tys.iter()) {
                                if b != "_" {
                                    arm_local.insert(b.clone(), pt.clone());
                                }
                            }
                        }
                    }
                    let bt = self.infer_expr(&arm.body, &mut arm_local, span)?;
                    res_ty = self.join_types(&bt, &res_ty, span)?;
                }

                // Exhaustiveness check for ADTs
                if let Type::Adt(adt_name) = self.apply(&scr_ty) {
                    if !has_wildcard {
                        if let Some(info) = self.adts.get(&adt_name) {
                            let missing: Vec<String> = info
                                .variants
                                .keys()
                                .filter(|k| !covered_variants.contains(*k))
                                .cloned()
                                .collect();
                            if !missing.is_empty() {
                                return Err(TypeError {
                                    message: format!(
                                        "Non-exhaustive match on '{}': missing variants [{}]",
                                        adt_name,
                                        missing.join(", ")
                                    ),
                                    span,
                                });
                            }
                        }
                    }
                }

                Ok(self.apply(&res_ty))
            }
            Expr::RecordInit { concept, fields } => {
                let cinfo = self.ontology.concepts.get(concept).cloned().ok_or_else(|| {
                    TypeError {
                        message: format!("Unknown OntoLogic concept '{}'", concept),
                        span,
                    }
                })?;

                let mut provided = BTreeSet::new();
                for (fname, fexpr) in fields {
                    let expected_fty_expr =
                        cinfo.all_fields.get(fname).cloned().ok_or_else(|| TypeError {
                            message: format!(
                                "Concept '{}' has no field '{}' (including inherited fields)",
                                concept, fname
                            ),
                            span,
                        })?;
                    let expected_fty = self.resolve_type_expr(&expected_fty_expr, span)?;
                    let actual_fty = self.infer_expr(fexpr, local, span)?;
                    self.unify(&actual_fty, &expected_fty, span)?;
                    provided.insert(fname.clone());
                }

                let missing: Vec<String> = cinfo
                    .all_fields
                    .keys()
                    .filter(|k| !provided.contains(*k))
                    .cloned()
                    .collect();
                if !missing.is_empty() {
                    return Err(TypeError {
                        message: format!(
                            "Missing fields in '{}' initialization: [{}]",
                            concept,
                            missing.join(", ")
                        ),
                        span,
                    });
                }

                Ok(Type::Concept(concept.clone()))
            }
            Expr::RecordWith { base, updates } => {
                let base_ty = self.infer_expr(base, local, span)?;
                let base_ty = self.apply(&base_ty);
                match &base_ty {
                    Type::Concept(cname) => {
                        let cinfo =
                            self.ontology.concepts.get(cname).cloned().ok_or_else(|| {
                                TypeError {
                                    message: format!("Unknown concept '{}'", cname),
                                    span,
                                }
                            })?;
                        for (fname, uexpr) in updates {
                            let fty_expr =
                                cinfo.all_fields.get(fname).cloned().ok_or_else(|| {
                                    TypeError {
                                        message: format!(
                                            "Concept '{}' has no field '{}'",
                                            cname, fname
                                        ),
                                        span,
                                    }
                                })?;
                            let expected_fty = self.resolve_type_expr(&fty_expr, span)?;
                            let actual_fty = self.infer_expr(uexpr, local, span)?;
                            self.unify(&actual_fty, &expected_fty, span)?;
                        }
                        Ok(base_ty)
                    }
                    other => Err(TypeError {
                        message: format!(
                            "Cannot apply 'with' record update to non-concept type {}",
                            other
                        ),
                        span,
                    }),
                }
            }
            Expr::FieldAccess { base, field } => {
                let base_ty = self.infer_expr(base, local, span)?;
                let base_ty = self.apply(&base_ty);
                match &base_ty {
                    Type::Concept(cname) => {
                        let cinfo =
                            self.ontology.concepts.get(cname).cloned().ok_or_else(|| {
                                TypeError {
                                    message: format!("Unknown concept '{}'", cname),
                                    span,
                                }
                            })?;
                        let fty_expr = cinfo.all_fields.get(field).cloned().ok_or_else(|| {
                            TypeError {
                                message: format!("Concept '{}' has no field '{}'", cname, field),
                                span,
                            }
                        })?;
                        self.resolve_type_expr(&fty_expr, span)
                    }
                    other => Err(TypeError {
                        message: format!("Cannot access field '{}' on type {}", field, other),
                        span,
                    }),
                }
            }
            Expr::Call { func, args } => {
                if let Some(builtin) = crate::builtins::BuiltinFn::from_name(func) {
                    match builtin {
                        crate::builtins::BuiltinFn::IsA if args.len() == 2 => {
                            let _ = self.infer_expr(&args[0], local, span)?;
                            let t2 = self.infer_expr(&args[1], local, span)?;
                            self.unify(&t2, &Type::Str, span)?;
                            return Ok(Type::Bool);
                        }
                        crate::builtins::BuiltinFn::Count if args.len() == 1 => {
                            let t = self.infer_expr(&args[0], local, span)?;
                            let elem = self.fresh_var();
                            self.unify(&t, &Type::List(Box::new(elem)), span)?;
                            return Ok(Type::Int);
                        }
                        _ => {}
                    }
                }

                let fn_ty = local.get(func).cloned().ok_or_else(|| TypeError {
                    message: format!("Unknown function or constructor '{}'", func),
                    span,
                })?;

                match self.apply(&fn_ty) {
                    Type::Fn(param_tys, ret_ty) => {
                        if args.len() != param_tys.len() {
                            return Err(TypeError {
                                message: format!(
                                    "'{}' expects {} arguments, got {}",
                                    func,
                                    param_tys.len(),
                                    args.len()
                                ),
                                span,
                            });
                        }
                        let mut placeholder_tys = Vec::new();
                        for (arg, expected_pt) in args.iter().zip(param_tys.iter()) {
                            if matches!(arg, Expr::Placeholder) && !local.contains_key("_") {
                                placeholder_tys.push(expected_pt.clone());
                            } else {
                                let at = self.infer_expr(arg, local, span)?;
                                self.unify(&at, expected_pt, span)?;
                            }
                        }
                        if placeholder_tys.is_empty() {
                            Ok(self.apply(&ret_ty))
                        } else {
                            Ok(Type::Fn(placeholder_tys, ret_ty))
                        }
                    }
                    other => Err(TypeError {
                        message: format!("'{}' is not callable (type {})", func, other),
                        span,
                    }),
                }
            }
            Expr::List(items) => {
                let elem_ty = self.fresh_var();
                let mut current_elem = elem_ty;
                for item in items {
                    let it = self.infer_expr(item, local, span)?;
                    current_elem = self.join_types(&it, &current_elem, span)?;
                }
                Ok(Type::List(Box::new(self.apply(&current_elem))))
            }
            Expr::LetIn { name, value, body } => {
                let vt = self.infer_expr(value, local, span)?;
                let mut inner_local = local.clone();
                inner_local.insert(name.clone(), vt);
                self.infer_expr(body, &mut inner_local, span)
            }
        }
    }

    fn infer_pipe(
        &mut self,
        left_ty: &Type,
        right: &Expr,
        local: &mut BTreeMap<String, Type>,
        span: Span,
    ) -> Result<Type, TypeError> {
        use crate::builtins::PipeStageBuiltin;
        let left_applied = self.apply(left_ty);
        if let Expr::Call { func, args } = right {
            match PipeStageBuiltin::from_name(func) {
                Some(PipeStageBuiltin::Where) if args.len() == 1 => {
                    let elem_ty = self.fresh_var();
                    self.unify(&left_applied, &Type::List(Box::new(elem_ty.clone())), span)?;
                    let elem_resolved = self.apply(&elem_ty);
                    let mut pred_local = local.clone();
                    pred_local.insert("_".into(), elem_resolved.clone());
                    let pt = self.infer_expr(&args[0], &mut pred_local, span)?;
                    if let Type::Fn(pargs, pret) = self.apply(&pt) {
                        if pargs.len() == 1 {
                            self.unify(&elem_resolved, &pargs[0], span)?;
                            self.unify(&pret, &Type::Bool, span)?;
                            return Ok(Type::List(Box::new(elem_resolved)));
                        }
                    }
                    self.unify(&pt, &Type::Bool, span)?;
                    return Ok(Type::List(Box::new(elem_resolved)));
                }
                Some(PipeStageBuiltin::Map) if args.len() == 1 => {
                    let elem_ty = self.fresh_var();
                    self.unify(&left_applied, &Type::List(Box::new(elem_ty.clone())), span)?;
                    let elem_resolved = self.apply(&elem_ty);
                    let mut map_local = local.clone();
                    map_local.insert("_".into(), elem_resolved.clone());
                    let mt = self.infer_expr(&args[0], &mut map_local, span)?;
                    if let Type::Fn(margs, mret) = self.apply(&mt) {
                        if margs.len() == 1 {
                            self.unify(&elem_resolved, &margs[0], span)?;
                            return Ok(Type::List(Box::new(self.apply(&mret))));
                        }
                    }
                    return Ok(Type::List(Box::new(self.apply(&mt))));
                }
                Some(PipeStageBuiltin::SortBy) if args.len() == 1 => {
                    let elem_ty = self.fresh_var();
                    self.unify(&left_applied, &Type::List(Box::new(elem_ty.clone())), span)?;
                    let elem_resolved = self.apply(&elem_ty);
                    let mut key_local = local.clone();
                    key_local.insert("_".into(), elem_resolved.clone());
                    let _ = self.infer_expr(&args[0], &mut key_local, span)?;
                    return Ok(Type::List(Box::new(elem_resolved)));
                }
                Some(PipeStageBuiltin::All | PipeStageBuiltin::Any) if args.len() == 1 => {
                    let elem_ty = self.fresh_var();
                    self.unify(&left_applied, &Type::List(Box::new(elem_ty.clone())), span)?;
                    let elem_resolved = self.apply(&elem_ty);
                    let mut pred_local = local.clone();
                    pred_local.insert("_".into(), elem_resolved.clone());
                    let pt = self.infer_expr(&args[0], &mut pred_local, span)?;
                    self.unify(&pt, &Type::Bool, span)?;
                    return Ok(Type::Bool);
                }
                Some(PipeStageBuiltin::Count) if args.is_empty() => {
                    let elem_ty = self.fresh_var();
                    self.unify(&left_applied, &Type::List(Box::new(elem_ty)), span)?;
                    return Ok(Type::Int);
                }
                Some(PipeStageBuiltin::Sum) if args.is_empty() => {
                    self.unify(&left_applied, &Type::List(Box::new(Type::Int)), span)?;
                    return Ok(Type::Int);
                }
                _ => {
                    // General pipe: x |> f(a, _) or x |> f(a)
                    let mut new_args = Vec::new();
                    let mut replaced = false;
                    for a in args {
                        if matches!(a, Expr::Placeholder) && !replaced {
                            replaced = true;
                        }
                        new_args.push(a.clone());
                    }
                    let mut pipe_local = local.clone();
                    if replaced {
                        pipe_local.insert("_".into(), left_applied);
                        let call_expr = Expr::Call {
                            func: func.clone(),
                            args: new_args,
                        };
                        return self.infer_expr(&call_expr, &mut pipe_local, span);
                    } else {
                        let fn_ty = local.get(func).cloned().ok_or_else(|| TypeError {
                            message: format!("Unknown function in pipeline '{}'", func),
                            span,
                        })?;
                        if let Type::Fn(param_tys, ret_ty) = self.apply(&fn_ty) {
                            if param_tys.len() != args.len() + 1 {
                                return Err(TypeError {
                                    message: format!(
                                        "Pipeline call to '{}' expects {} args, got {}",
                                        func,
                                        param_tys.len(),
                                        args.len() + 1
                                    ),
                                    span,
                                });
                            }
                            self.unify(&left_applied, &param_tys[0], span)?;
                            for (a, pt) in args.iter().zip(param_tys[1..].iter()) {
                                let at = self.infer_expr(a, local, span)?;
                                self.unify(&at, pt, span)?;
                            }
                            return Ok(self.apply(&ret_ty));
                        }
                    }
                }
            }
        } else if let Expr::Var(func) = right {
            return self.infer_pipe(
                left_ty,
                &Expr::Call {
                    func: func.clone(),
                    args: vec![],
                },
                local,
                span,
            );
        }

        Err(TypeError {
            message: "Right-hand side of '|>' must be a function call or pipeline stage".into(),
            span,
        })
    }
}
