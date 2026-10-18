use crate::ast::{BinOp, Pattern, QuantifierKind, UnaryOp};
use crate::ir::hir::{HirExpr, HirExprKind, HirGclBody, HirProgram};
use crate::types::Type;
use std::fmt;

/// Level 3 IR: Low-Level Ghost-Erased Executable IR (LIR).
/// - Performs **Ghost Erasure**: strips `axiom`, `spec`, `requires`, `ensures`, `invariant`, and `variant`
///   annotations once verified in VIR, leaving zero runtime proof overhead.
/// - Lowers Guarded Command Language (`if..fi`, `do..od`) and `|>` pipelines into structured executable nodes.
#[derive(Debug, Clone)]
pub struct LirProgram {
    pub functions: Vec<LirFn>,
    pub globals: Vec<(String, Type, LirExpr)>,
    pub assertions: Vec<LirExpr>,
    pub erased_ghost_count: usize,
}

#[derive(Debug, Clone)]
pub struct LirFn {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret_ty: Type,
    pub body: LirExpr,
}

#[derive(Debug, Clone)]
pub enum LirExpr {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Var(String),
    Placeholder,
    Unary(UnaryOp, Box<LirExpr>),
    Binary(BinOp, Box<LirExpr>, Box<LirExpr>),
    Quantifier {
        kind: QuantifierKind,
        var: String,
        domain: Box<LirExpr>,
        body: Box<LirExpr>,
    },
    /// Lowered Guarded Branch Table (invariant/totality already proved in VIR)
    GuardedSelect {
        branches: Vec<(LirExpr, LirAction)>,
    },
    /// Ghost-erased Guarded Loop (`invariant` and `variant` erased after VIR proof)
    GuardedLoop {
        inits: Vec<(String, LirExpr)>,
        branches: Vec<(LirExpr, LirAction)>,
        then_expr: Box<LirExpr>,
    },
    Match {
        scrutinee: Box<LirExpr>,
        arms: Vec<(Pattern, LirExpr)>,
    },
    StructInit {
        name: String,
        fields: Vec<(String, LirExpr)>,
    },
    StructUpdate {
        base: Box<LirExpr>,
        updates: Vec<(String, LirExpr)>,
    },
    Field {
        base: Box<LirExpr>,
        field: String,
    },
    Call {
        func: String,
        args: Vec<LirExpr>,
    },
    PipeStage {
        stage: String,
        input: Box<LirExpr>,
        arg: Option<Box<LirExpr>>,
    },
    List(Vec<LirExpr>),
    LetIn {
        name: String,
        value: Box<LirExpr>,
        body: Box<LirExpr>,
    },
}

#[derive(Debug, Clone)]
pub enum LirAction {
    ReturnExpr(LirExpr),
    AssignState(Vec<(String, LirExpr)>),
    Nop,
    TrapAbort,
}

impl LirProgram {
    pub fn lower_with_ghost_erasure(hir: &HirProgram) -> Self {
        let mut erased_ghost_count = hir.axioms.len() + hir.specs.len() + hir.proofs.len();

        let mut functions = Vec::new();
        for f in &hir.functions {
            if f.requires.is_some() {
                erased_ghost_count += 1;
            }
            if f.ensures.is_some() {
                erased_ghost_count += 1;
            }
            if f.refines.is_some() {
                erased_ghost_count += 1;
            }
            let body = lower_hir_expr(&f.body, &mut erased_ghost_count);
            functions.push(LirFn {
                name: f.name.clone(),
                params: f.params.clone(),
                ret_ty: f.ret_ty.clone(),
                body,
            });
        }

        let mut globals = Vec::new();
        for b in &hir.bindings {
            let val = lower_hir_expr(&b.value, &mut erased_ghost_count);
            globals.push((b.name.clone(), b.ty.clone(), val));
        }

        let mut assertions = Vec::new();
        for a in &hir.asserts {
            assertions.push(lower_hir_expr(a, &mut erased_ghost_count));
        }

        LirProgram {
            functions,
            globals,
            assertions,
            erased_ghost_count,
        }
    }
}

fn lower_hir_expr(expr: &HirExpr, erased: &mut usize) -> LirExpr {
    match &expr.kind {
        HirExprKind::Int(v) => LirExpr::Int(*v),
        HirExprKind::Float(v) => LirExpr::Float(*v),
        HirExprKind::Bool(v) => LirExpr::Bool(*v),
        HirExprKind::Str(v) => LirExpr::Str(v.clone()),
        HirExprKind::Var(v) => LirExpr::Var(v.clone()),
        HirExprKind::Placeholder => LirExpr::Placeholder,
        HirExprKind::Unary(op, inner) => {
            LirExpr::Unary(*op, Box::new(lower_hir_expr(inner, erased)))
        }
        HirExprKind::Binary(op, l, r) => LirExpr::Binary(
            *op,
            Box::new(lower_hir_expr(l, erased)),
            Box::new(lower_hir_expr(r, erased)),
        ),
        HirExprKind::Quantifier {
            kind,
            var,
            domain,
            body,
        } => LirExpr::Quantifier {
            kind: kind.clone(),
            var: var.clone(),
            domain: Box::new(lower_hir_expr(domain, erased)),
            body: Box::new(lower_hir_expr(body, erased)),
        },
        HirExprKind::IfFi { branches } => LirExpr::GuardedSelect {
            branches: branches
                .iter()
                .map(|(g, b)| (lower_hir_expr(g, erased), lower_hir_action(b, erased)))
                .collect(),
        },
        HirExprKind::DoOd {
            inits,
            invariant,
            variant,
            branches,
            then_expr,
        } => {
            // Erase ghost loop invariant & variant in LIR
            if invariant.is_some() {
                *erased += 1;
            }
            if variant.is_some() {
                *erased += 1;
            }
            LirExpr::GuardedLoop {
                inits: inits
                    .iter()
                    .map(|(n, _, ie)| (n.clone(), lower_hir_expr(ie, erased)))
                    .collect(),
                branches: branches
                    .iter()
                    .map(|(g, b)| (lower_hir_expr(g, erased), lower_hir_action(b, erased)))
                    .collect(),
                then_expr: Box::new(lower_hir_expr(then_expr, erased)),
            }
        }
        HirExprKind::Match { scrutinee, arms } => LirExpr::Match {
            scrutinee: Box::new(lower_hir_expr(scrutinee, erased)),
            arms: arms
                .iter()
                .map(|(p, e)| (p.clone(), lower_hir_expr(e, erased)))
                .collect(),
        },
        HirExprKind::RecordInit { concept, fields } => LirExpr::StructInit {
            name: concept.clone(),
            fields: fields
                .iter()
                .map(|(k, v)| (k.clone(), lower_hir_expr(v, erased)))
                .collect(),
        },
        HirExprKind::RecordWith { base, updates } => LirExpr::StructUpdate {
            base: Box::new(lower_hir_expr(base, erased)),
            updates: updates
                .iter()
                .map(|(k, v)| (k.clone(), lower_hir_expr(v, erased)))
                .collect(),
        },
        HirExprKind::FieldAccess { base, field } => LirExpr::Field {
            base: Box::new(lower_hir_expr(base, erased)),
            field: field.clone(),
        },
        HirExprKind::Call { func, args } => LirExpr::Call {
            func: func.clone(),
            args: args.iter().map(|a| lower_hir_expr(a, erased)).collect(),
        },
        HirExprKind::PipeStage { stage, input, arg } => LirExpr::PipeStage {
            stage: stage.clone(),
            input: Box::new(lower_hir_expr(input, erased)),
            arg: arg.as_ref().map(|a| Box::new(lower_hir_expr(a, erased))),
        },
        HirExprKind::List(items) => {
            LirExpr::List(items.iter().map(|i| lower_hir_expr(i, erased)).collect())
        }
        HirExprKind::LetIn { name, value, body } => LirExpr::LetIn {
            name: name.clone(),
            value: Box::new(lower_hir_expr(value, erased)),
            body: Box::new(lower_hir_expr(body, erased)),
        },
    }
}

fn lower_hir_action(body: &HirGclBody, erased: &mut usize) -> LirAction {
    match body {
        HirGclBody::Expr(e) => LirAction::ReturnExpr(lower_hir_expr(e, erased)),
        HirGclBody::Updates(ups) => LirAction::AssignState(
            ups.iter()
                .map(|(v, ue)| (v.clone(), lower_hir_expr(ue, erased)))
                .collect(),
        ),
        HirGclBody::Skip => LirAction::Nop,
        HirGclBody::Abort => LirAction::TrapAbort,
    }
}

impl fmt::Display for LirProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "=== Level 3: LIR (Ghost-Erased Executable Control & Dataflow IR — {} ghost items erased) ===",
            self.erased_ghost_count
        )?;
        for func in &self.functions {
            let ps: Vec<String> = func
                .params
                .iter()
                .map(|(n, t)| format!("{}: {}", n, t))
                .collect();
            writeln!(f, "  exec_fn {}({}) -> {}", func.name, ps.join(", "), func.ret_ty)?;
        }
        for (gname, gty, _) in &self.globals {
            writeln!(f, "  global {}: {}", gname, gty)?;
        }
        Ok(())
    }
}
