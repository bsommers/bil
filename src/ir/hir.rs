use crate::ast::*;
use crate::ontology::OntologyRegistry;
use crate::types::{Type, TypeEnv};
use std::collections::BTreeMap;
use std::fmt;

/// Level 1 IR: High-Level Ontology & Typed Logic IR (HIR).
/// - Flattens BFO `concept` inheritance into complete resolved field layouts.
/// - Desugars `|>` pipelines into explicit `PipeStage` or direct function calls.
/// - Annotates declarations and expressions with resolved Hindley-Milner + subtyping `Type`s.
#[derive(Debug, Clone)]
pub struct HirProgram {
    pub concepts: Vec<HirConcept>,
    pub adts: Vec<HirAdt>,
    pub axioms: Vec<HirAxiom>,
    pub specs: Vec<HirSpec>,
    pub proofs: Vec<HirProof>,
    pub functions: Vec<HirFn>,
    pub systems: Vec<HirSystem>,
    pub bindings: Vec<HirLet>,
    pub asserts: Vec<HirExpr>,
}

#[derive(Debug, Clone)]
pub struct HirConcept {
    pub name: String,
    pub ancestors: Vec<String>,
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone)]
pub struct HirAdt {
    pub name: String,
    pub variants: Vec<(String, Vec<Type>)>,
}

#[derive(Debug, Clone)]
pub struct HirAxiom {
    pub name: String,
    pub formula: HirExpr,
}

#[derive(Debug, Clone)]
pub struct HirSpec {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret_ty: Type,
    pub requires: Option<HirExpr>,
    pub ensures: Option<HirExpr>,
}

#[derive(Debug, Clone)]
pub struct HirProof {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub requires: Option<HirExpr>,
    pub ensures: Option<HirExpr>,
    pub body: HirExpr,
}

#[derive(Debug, Clone)]
pub struct HirFn {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret_ty: Type,
    pub refines: Option<String>,
    pub requires: Option<HirExpr>,
    pub ensures: Option<HirExpr>,
    pub body: HirExpr,
}

#[derive(Debug, Clone)]
pub enum HirTemporalFormula {
    Always(HirExpr),
    Eventually(HirExpr),
    LeadsTo(HirExpr, HirExpr),
}

#[derive(Debug, Clone)]
pub struct HirSystem {
    pub name: String,
    pub states: Vec<(String, Type, HirExpr)>,
    pub invariants: Vec<(String, HirExpr)>,
    pub temporals: Vec<(String, HirTemporalFormula)>,
    pub variant: Option<HirExpr>,
    pub terminal: Option<HirExpr>,
    pub transitions: Vec<(HirExpr, Vec<(String, HirExpr)>)>,
}

#[derive(Debug, Clone)]
pub struct HirLet {
    pub name: String,
    pub ty: Type,
    pub value: HirExpr,
}

#[derive(Debug, Clone)]
pub struct HirExpr {
    pub kind: HirExprKind,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub enum HirExprKind {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Var(String),
    Placeholder,
    Unary(UnaryOp, Box<HirExpr>),
    Binary(BinOp, Box<HirExpr>, Box<HirExpr>),
    Quantifier {
        kind: QuantifierKind,
        var: String,
        domain: Box<HirExpr>,
        body: Box<HirExpr>,
    },
    IfFi {
        branches: Vec<(HirExpr, HirGclBody)>,
    },
    DoOd {
        inits: Vec<(String, Type, HirExpr)>,
        invariant: Option<Box<HirExpr>>,
        variant: Option<Box<HirExpr>>,
        branches: Vec<(HirExpr, HirGclBody)>,
        then_expr: Box<HirExpr>,
    },
    Match {
        scrutinee: Box<HirExpr>,
        arms: Vec<(Pattern, HirExpr)>,
    },
    RecordInit {
        concept: String,
        fields: Vec<(String, HirExpr)>,
    },
    RecordWith {
        base: Box<HirExpr>,
        updates: Vec<(String, HirExpr)>,
    },
    FieldAccess {
        base: Box<HirExpr>,
        field: String,
    },
    Call {
        func: String,
        args: Vec<HirExpr>,
    },
    /// Desugared pipeline stage: `input |> op(arg)`
    PipeStage {
        stage: String,
        input: Box<HirExpr>,
        arg: Option<Box<HirExpr>>,
    },
    List(Vec<HirExpr>),
    LetIn {
        name: String,
        value: Box<HirExpr>,
        body: Box<HirExpr>,
    },
}

#[derive(Debug, Clone)]
pub enum HirGclBody {
    Expr(HirExpr),
    Updates(Vec<(String, HirExpr)>),
    Skip,
    Abort,
}

impl HirProgram {
    pub fn lower(program: &Program, ontology: &OntologyRegistry, tenv: &mut TypeEnv) -> Self {
        let dummy_span = crate::lexer::Span::new(1, 1);

        let mut concepts = Vec::new();
        for (cname, cinfo) in &ontology.concepts {
            let mut ancestors = Vec::new();
            let mut cur = cinfo.parent.clone();
            while let Some(p) = cur {
                ancestors.push(p.clone());
                cur = ontology.concepts.get(&p).and_then(|ci| ci.parent.clone());
            }
            let mut fields = Vec::new();
            for (fname, fty_expr) in &cinfo.all_fields {
                let ty = tenv
                    .resolve_type_expr(fty_expr, dummy_span)
                    .unwrap_or(Type::Unit);
                fields.push((fname.clone(), ty));
            }
            concepts.push(HirConcept {
                name: cname.clone(),
                ancestors,
                fields,
            });
        }

        let mut adts = Vec::new();
        for (aname, ainfo) in &tenv.adts {
            let variants = ainfo
                .variants
                .iter()
                .map(|(v, tys)| (v.clone(), tys.clone()))
                .collect();
            adts.push(HirAdt {
                name: aname.clone(),
                variants,
            });
        }

        let mut axioms = Vec::new();
        let mut specs = Vec::new();
        let mut proofs = Vec::new();
        let mut functions = Vec::new();
        let mut systems = Vec::new();
        let mut bindings = Vec::new();
        let mut asserts = Vec::new();

        for item in &program.items {
            match item {
                Item::Concept(_) | Item::TypeDecl(_) => {}
                Item::Axiom(ax) => {
                    let mut local = tenv.bindings.clone();
                    let formula = lower_expr(&ax.formula, tenv, &mut local);
                    axioms.push(HirAxiom {
                        name: ax.name.clone(),
                        formula,
                    });
                }
                Item::Spec(sp) => {
                    let mut local = tenv.bindings.clone();
                    let mut params = Vec::new();
                    for p in &sp.params {
                        let pt = tenv.resolve_type_expr(&p.ty, sp.span).unwrap_or(Type::Unit);
                        local.insert(p.name.clone(), pt.clone());
                        params.push((p.name.clone(), pt));
                    }
                    let ret_ty = tenv
                        .resolve_type_expr(&sp.ret_ty, sp.span)
                        .unwrap_or(Type::Unit);
                    let requires = sp
                        .requires
                        .as_ref()
                        .map(|r| lower_expr(r, tenv, &mut local));
                    local.insert("result".into(), ret_ty.clone());
                    let ensures = sp
                        .ensures
                        .as_ref()
                        .map(|e| lower_expr(e, tenv, &mut local));
                    specs.push(HirSpec {
                        name: sp.name.clone(),
                        params,
                        ret_ty,
                        requires,
                        ensures,
                    });
                }
                Item::Proof(pr) => {
                    let mut local = tenv.bindings.clone();
                    let mut params = Vec::new();
                    for p in &pr.params {
                        let pt = tenv.resolve_type_expr(&p.ty, pr.span).unwrap_or(Type::Unit);
                        local.insert(p.name.clone(), pt.clone());
                        params.push((p.name.clone(), pt));
                    }
                    let requires = pr
                        .requires
                        .as_ref()
                        .map(|r| lower_expr(r, tenv, &mut local));
                    let ensures = Some(lower_expr(&pr.ensures, tenv, &mut local));
                    let body = pr
                        .body
                        .as_ref()
                        .map(|b| lower_expr(b, tenv, &mut local))
                        .unwrap_or_else(|| lower_expr(&Expr::Bool(true), tenv, &mut local));
                    proofs.push(HirProof {
                        name: pr.name.clone(),
                        params,
                        requires,
                        ensures,
                        body,
                    });
                }
                Item::FnDecl(f) => {
                    let mut local = tenv.bindings.clone();
                    let mut params = Vec::new();
                    for p in &f.params {
                        let pt = tenv.resolve_type_expr(&p.ty, f.span).unwrap_or(Type::Unit);
                        local.insert(p.name.clone(), pt.clone());
                        params.push((p.name.clone(), pt));
                    }
                    let ret_ty = tenv
                        .resolve_type_expr(&f.ret_ty, f.span)
                        .unwrap_or(Type::Unit);
                    let requires = f
                        .requires
                        .as_ref()
                        .map(|r| lower_expr(r, tenv, &mut local));
                    let body = lower_expr(&f.body, tenv, &mut local);
                    local.insert("result".into(), ret_ty.clone());
                    let ensures = f
                        .ensures
                        .as_ref()
                        .map(|e| lower_expr(e, tenv, &mut local));
                    functions.push(HirFn {
                        name: f.name.clone(),
                        params,
                        ret_ty,
                        refines: f.refines.clone(),
                        requires,
                        ensures,
                        body,
                    });
                }
                Item::System(sys) => {
                    let mut local = tenv.bindings.clone();
                    let mut states = Vec::new();
                    for st in &sys.states {
                        let sty = tenv
                            .resolve_type_expr(&st.ty, sys.span)
                            .unwrap_or(Type::Unit);
                        let init = lower_expr(&st.init, tenv, &mut local);
                        local.insert(st.name.clone(), sty.clone());
                        states.push((st.name.clone(), sty, init));
                    }
                    let invariants = sys
                        .invariants
                        .iter()
                        .map(|inv| (inv.name.clone(), lower_expr(&inv.formula, tenv, &mut local)))
                        .collect();
                    let temporals = sys
                        .temporals
                        .iter()
                        .map(|t| {
                            let tf = match &t.formula {
                                TemporalFormula::Always(e) => {
                                    HirTemporalFormula::Always(lower_expr(e, tenv, &mut local))
                                }
                                TemporalFormula::Eventually(e) => {
                                    HirTemporalFormula::Eventually(lower_expr(e, tenv, &mut local))
                                }
                                TemporalFormula::LeadsTo(p, q) => HirTemporalFormula::LeadsTo(
                                    lower_expr(p, tenv, &mut local),
                                    lower_expr(q, tenv, &mut local),
                                ),
                            };
                            (t.name.clone(), tf)
                        })
                        .collect();
                    let variant = sys
                        .variant
                        .as_ref()
                        .map(|v| lower_expr(v, tenv, &mut local));
                    let terminal = sys
                        .terminal
                        .as_ref()
                        .map(|t| lower_expr(t, tenv, &mut local));
                    let transitions = sys
                        .transitions
                        .iter()
                        .map(|tr| {
                            let g = lower_expr(&tr.guard, tenv, &mut local);
                            let ups = tr
                                .updates
                                .iter()
                                .map(|(v, ue)| (v.clone(), lower_expr(ue, tenv, &mut local)))
                                .collect();
                            (g, ups)
                        })
                        .collect();
                    systems.push(HirSystem {
                        name: sys.name.clone(),
                        states,
                        invariants,
                        temporals,
                        variant,
                        terminal,
                        transitions,
                    });
                }
                Item::Let(l) => {
                    let mut local = tenv.bindings.clone();
                    let val = lower_expr(&l.value, tenv, &mut local);
                    bindings.push(HirLet {
                        name: l.name.clone(),
                        ty: val.ty.clone(),
                        value: val,
                    });
                }
                Item::Assert(a) => {
                    let mut local = tenv.bindings.clone();
                    asserts.push(lower_expr(&a.formula, tenv, &mut local));
                }
            }
        }

        HirProgram {
            concepts,
            adts,
            axioms,
            specs,
            proofs,
            functions,
            systems,
            bindings,
            asserts,
        }
    }
}

fn lower_expr(expr: &Expr, tenv: &mut TypeEnv, local: &mut BTreeMap<String, Type>) -> HirExpr {
    let span = crate::lexer::Span::new(1, 1);
    let inferred_ty = tenv
        .infer_expr(expr, local, span)
        .map(|t| tenv.apply(&t))
        .unwrap_or(Type::Unit);

    let kind = match expr {
        Expr::Int(v) => HirExprKind::Int(*v),
        Expr::Float(v) => HirExprKind::Float(*v),
        Expr::Bool(v) => HirExprKind::Bool(*v),
        Expr::Str(v) => HirExprKind::Str(v.clone()),
        Expr::Var(v) => HirExprKind::Var(v.clone()),
        Expr::Placeholder => HirExprKind::Placeholder,
        Expr::Unary { op, expr: inner } => {
            HirExprKind::Unary(*op, Box::new(lower_expr(inner, tenv, local)))
        }
        Expr::Binary {
            op: BinOp::Pipe,
            left,
            right,
        } => {
            // Desugar `left |> stage(arg)` into explicit `PipeStage` HIR node
            let l_hir = lower_expr(left, tenv, local);
            if let Expr::Call { func, args } = &**right {
                let mut stage_local = local.clone();
                if let Type::List(elem) = &l_hir.ty {
                    stage_local.insert("_".into(), (**elem).clone());
                } else {
                    stage_local.insert("_".into(), l_hir.ty.clone());
                }
                let arg_hir = args
                    .first()
                    .map(|a| Box::new(lower_expr(a, tenv, &mut stage_local)));
                HirExprKind::PipeStage {
                    stage: func.clone(),
                    input: Box::new(l_hir),
                    arg: arg_hir,
                }
            } else {
                let r_hir = lower_expr(right, tenv, local);
                HirExprKind::Binary(BinOp::Pipe, Box::new(l_hir), Box::new(r_hir))
            }
        }
        Expr::Binary { op, left, right } => HirExprKind::Binary(
            *op,
            Box::new(lower_expr(left, tenv, local)),
            Box::new(lower_expr(right, tenv, local)),
        ),
        Expr::Quantifier {
            kind,
            var,
            domain,
            body,
        } => {
            let dom_hir = lower_expr(domain, tenv, local);
            let mut inner_local = local.clone();
            if let Type::List(elem) = &dom_hir.ty {
                inner_local.insert(var.clone(), (**elem).clone());
            } else {
                inner_local.insert(var.clone(), Type::Int);
            }
            let body_hir = lower_expr(body, tenv, &mut inner_local);
            HirExprKind::Quantifier {
                kind: kind.clone(),
                var: var.clone(),
                domain: Box::new(dom_hir),
                body: Box::new(body_hir),
            }
        }
        Expr::IfFi { branches } => {
            let brs = branches
                .iter()
                .map(|b| {
                    let g = lower_expr(&b.guard, tenv, local);
                    let body = lower_gcl_body(&b.body, tenv, local);
                    (g, body)
                })
                .collect();
            HirExprKind::IfFi { branches: brs }
        }
        Expr::DoOd {
            inits,
            invariant,
            variant,
            branches,
            then_expr,
        } => {
            let mut loop_local = local.clone();
            let mut hir_inits = Vec::new();
            for (vname, iexpr) in inits {
                let ih = lower_expr(iexpr, tenv, &mut loop_local);
                loop_local.insert(vname.clone(), ih.ty.clone());
                hir_inits.push((vname.clone(), ih.ty.clone(), ih));
            }
            let inv_hir = invariant
                .as_ref()
                .map(|i| Box::new(lower_expr(i, tenv, &mut loop_local)));
            let var_hir = variant
                .as_ref()
                .map(|v| Box::new(lower_expr(v, tenv, &mut loop_local)));
            let brs = branches
                .iter()
                .map(|b| {
                    let g = lower_expr(&b.guard, tenv, &mut loop_local);
                    let body = lower_gcl_body(&b.body, tenv, &mut loop_local);
                    (g, body)
                })
                .collect();
            let then_hir = lower_expr(then_expr, tenv, &mut loop_local);
            HirExprKind::DoOd {
                inits: hir_inits,
                invariant: inv_hir,
                variant: var_hir,
                branches: brs,
                then_expr: Box::new(then_hir),
            }
        }
        Expr::Match { scrutinee, arms } => {
            let scr = lower_expr(scrutinee, tenv, local);
            let hir_arms = arms
                .iter()
                .map(|a| (a.pattern.clone(), lower_expr(&a.body, tenv, local)))
                .collect();
            HirExprKind::Match {
                scrutinee: Box::new(scr),
                arms: hir_arms,
            }
        }
        Expr::RecordInit { concept, fields } => HirExprKind::RecordInit {
            concept: concept.clone(),
            fields: fields
                .iter()
                .map(|(k, v)| (k.clone(), lower_expr(v, tenv, local)))
                .collect(),
        },
        Expr::RecordWith { base, updates } => HirExprKind::RecordWith {
            base: Box::new(lower_expr(base, tenv, local)),
            updates: updates
                .iter()
                .map(|(k, v)| (k.clone(), lower_expr(v, tenv, local)))
                .collect(),
        },
        Expr::FieldAccess { base, field } => HirExprKind::FieldAccess {
            base: Box::new(lower_expr(base, tenv, local)),
            field: field.clone(),
        },
        Expr::Call { func, args } => HirExprKind::Call {
            func: func.clone(),
            args: args.iter().map(|a| lower_expr(a, tenv, local)).collect(),
        },
        Expr::List(items) => {
            HirExprKind::List(items.iter().map(|i| lower_expr(i, tenv, local)).collect())
        }
        Expr::LetIn { name, value, body } => {
            let v = lower_expr(value, tenv, local);
            let mut inner = local.clone();
            inner.insert(name.clone(), v.ty.clone());
            let b = lower_expr(body, tenv, &mut inner);
            HirExprKind::LetIn {
                name: name.clone(),
                value: Box::new(v),
                body: Box::new(b),
            }
        }
    };

    HirExpr {
        kind,
        ty: inferred_ty,
    }
}

fn lower_gcl_body(
    body: &GclBody,
    tenv: &mut TypeEnv,
    local: &mut BTreeMap<String, Type>,
) -> HirGclBody {
    match body {
        GclBody::Expr(e) => HirGclBody::Expr(lower_expr(e, tenv, local)),
        GclBody::Updates(ups) => HirGclBody::Updates(
            ups.iter()
                .map(|(v, ue)| (v.clone(), lower_expr(ue, tenv, local)))
                .collect(),
        ),
        GclBody::Skip => HirGclBody::Skip,
        GclBody::Abort => HirGclBody::Abort,
    }
}

impl fmt::Display for HirProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Level 1: HIR (Ontology & Typed Logic IR) ===")?;
        for c in &self.concepts {
            let anc = if c.ancestors.is_empty() {
                String::new()
            } else {
                format!(" <: {}", c.ancestors.join(" <: "))
            };
            let fs: Vec<String> = c
                .fields
                .iter()
                .map(|(n, t)| format!("{}: {}", n, t))
                .collect();
            writeln!(f, "  concept {}{} {{ {} }}", c.name, anc, fs.join(", "))?;
        }
        for ax in &self.axioms {
            writeln!(f, "  axiom {} : {}", ax.name, ax.formula.ty)?;
        }
        for sp in &self.specs {
            let ps: Vec<String> = sp
                .params
                .iter()
                .map(|(n, t)| format!("{}: {}", n, t))
                .collect();
            writeln!(f, "  spec {}({}) -> {}", sp.name, ps.join(", "), sp.ret_ty)?;
        }
        for pr in &self.proofs {
            let ps: Vec<String> = pr
                .params
                .iter()
                .map(|(n, t)| format!("{}: {}", n, t))
                .collect();
            writeln!(f, "  proof {}({}) [ghost lemma]", pr.name, ps.join(", "))?;
        }
        for func in &self.functions {
            let ps: Vec<String> = func
                .params
                .iter()
                .map(|(n, t)| format!("{}: {}", n, t))
                .collect();
            let ref_s = func
                .refines
                .as_ref()
                .map(|r| format!(" refines {}", r))
                .unwrap_or_default();
            writeln!(
                f,
                "  fn {}({}) -> {}{} [body: {}]",
                func.name,
                ps.join(", "),
                func.ret_ty,
                ref_s,
                func.body.ty
            )?;
        }
        for sys in &self.systems {
            writeln!(
                f,
                "  system {} ({} states, {} invariants, {} transitions)",
                sys.name,
                sys.states.len(),
                sys.invariants.len(),
                sys.transitions.len()
            )?;
        }
        for b in &self.bindings {
            writeln!(f, "  let {}: {}", b.name, b.ty)?;
        }
        Ok(())
    }
}
