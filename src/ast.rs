use crate::lexer::Span;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Program {
    pub items: Vec<Item>,
    /// Source span of every expression node, in [`Program::for_each_expr_postorder`] order.
    /// Filled by the parser; empty for programs built in code, which then fall back to
    /// item-level spans in diagnostics.
    pub expr_spans: Vec<Span>,
}

impl Program {
    /// Visits every expression node, item by item, in post-order (children before parents).
    /// This order is the contract for `expr_spans`: the parser records spans in exactly
    /// this order, so change both together.
    pub fn for_each_expr_postorder(&self, f: &mut dyn FnMut(&Expr)) {
        for item in &self.items {
            item.for_each_expr_postorder(f);
        }
    }
}

impl Item {
    /// One item's share of [`Program::for_each_expr_postorder`].
    pub fn for_each_expr_postorder(&self, f: &mut dyn FnMut(&Expr)) {
        let item = self;
        match item {
            Item::Concept(_) | Item::TypeDecl(_) => {}
            Item::Axiom(ax) => ax.formula.walk_postorder(f),
            Item::Spec(sp) => {
                sp.requires.iter().for_each(|e| e.walk_postorder(f));
                sp.ensures.iter().for_each(|e| e.walk_postorder(f));
            }
            Item::Proof(pr) => {
                pr.requires.iter().for_each(|e| e.walk_postorder(f));
                pr.ensures.walk_postorder(f);
                pr.body.iter().for_each(|e| e.walk_postorder(f));
            }
            Item::FnDecl(fd) => {
                fd.requires.iter().for_each(|e| e.walk_postorder(f));
                fd.ensures.iter().for_each(|e| e.walk_postorder(f));
                fd.variant.iter().for_each(|e| e.walk_postorder(f));
                fd.body.walk_postorder(f);
            }
            Item::System(sys) => {
                sys.states.iter().for_each(|s| s.init.walk_postorder(f));
                sys.invariants
                    .iter()
                    .for_each(|i| i.formula.walk_postorder(f));
                for t in &sys.temporals {
                    match &t.formula {
                        TemporalFormula::Always(e) | TemporalFormula::Eventually(e) => {
                            e.walk_postorder(f)
                        }
                        TemporalFormula::LeadsTo(p, q) => {
                            p.walk_postorder(f);
                            q.walk_postorder(f);
                        }
                    }
                }
                sys.variant.iter().for_each(|e| e.walk_postorder(f));
                sys.terminal.iter().for_each(|e| e.walk_postorder(f));
                for tr in &sys.transitions {
                    tr.guard.walk_postorder(f);
                    tr.updates.iter().for_each(|(_, e)| e.walk_postorder(f));
                }
                for d in &sys.deadlines {
                    d.latch.walk_postorder(f);
                    d.response.walk_postorder(f);
                    d.phase.iter().for_each(|e| e.walk_postorder(f));
                }
            }
            Item::Let(l) => l.value.walk_postorder(f),
            Item::Assert(a) => a.formula.walk_postorder(f),
        }
    }
}

impl Expr {
    /// Post-order walk over this expression; children are visited in source order.
    pub fn walk_postorder(&self, f: &mut dyn FnMut(&Expr)) {
        let gcl = |br: &GuardedBranch, f: &mut dyn FnMut(&Expr)| {
            br.guard.walk_postorder(f);
            match &br.body {
                GclBody::Expr(e) => e.walk_postorder(f),
                GclBody::Updates(ups) => ups.iter().for_each(|(_, e)| e.walk_postorder(f)),
                GclBody::Skip | GclBody::Abort => {}
            }
        };
        match self {
            Expr::Int(_)
            | Expr::Float(_)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::Var(_)
            | Expr::Placeholder => {}
            Expr::Unary { expr, .. } => expr.walk_postorder(f),
            Expr::Binary { left, right, .. } => {
                left.walk_postorder(f);
                right.walk_postorder(f);
            }
            Expr::Quantifier { domain, body, .. } => {
                domain.walk_postorder(f);
                body.walk_postorder(f);
            }
            Expr::IfFi { branches } => branches.iter().for_each(|br| gcl(br, f)),
            Expr::DoOd {
                inits,
                invariant,
                variant,
                branches,
                then_expr,
            } => {
                inits.iter().for_each(|(_, e)| e.walk_postorder(f));
                invariant.iter().for_each(|e| e.walk_postorder(f));
                variant.iter().for_each(|e| e.walk_postorder(f));
                branches.iter().for_each(|br| gcl(br, f));
                then_expr.walk_postorder(f);
            }
            Expr::Match { scrutinee, arms } => {
                scrutinee.walk_postorder(f);
                arms.iter().for_each(|a| a.body.walk_postorder(f));
            }
            Expr::RecordInit { fields, .. } => fields.iter().for_each(|(_, e)| e.walk_postorder(f)),
            Expr::RecordWith { base, updates } => {
                base.walk_postorder(f);
                updates.iter().for_each(|(_, e)| e.walk_postorder(f));
            }
            Expr::FieldAccess { base, .. } => base.walk_postorder(f),
            Expr::Call { args, .. } => args.iter().for_each(|e| e.walk_postorder(f)),
            Expr::List(items) => items.iter().for_each(|e| e.walk_postorder(f)),
            Expr::LetIn { value, body, .. } => {
                value.walk_postorder(f);
                body.walk_postorder(f);
            }
        }
        f(self);
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Concept(ConceptDecl),
    TypeDecl(AdtDecl),
    Axiom(AxiomDecl),
    Spec(SpecDecl),
    Proof(ProofDecl),
    FnDecl(FnDecl),
    System(SystemDecl),
    Let(LetDecl),
    Assert(AssertDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ProofDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub requires: Option<Expr>,
    pub ensures: Expr,
    pub body: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConceptDecl {
    pub name: String,
    pub parent: Option<String>,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantDecl {
    pub name: String,
    pub payload: Vec<TypeExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AdtDecl {
    pub name: String,
    pub variants: Vec<VariantDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AxiomDecl {
    pub name: String,
    pub formula: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpecDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: TypeExpr,
    pub requires: Option<Expr>,
    pub ensures: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: TypeExpr,
    pub refines: Option<String>,
    pub requires: Option<Expr>,
    pub ensures: Option<Expr>,
    /// Termination measure for recursive calls: a non-negative Int that every recursive call
    /// must strictly decrease. Lets the verifier use the function's own contract at those calls.
    pub variant: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StateVarDecl {
    pub name: String,
    pub ty: TypeExpr,
    pub init: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct NamedInvariant {
    pub name: String,
    pub formula: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TemporalFormula {
    /// □P — safety / invariance across all reachable states
    Always(Expr),
    /// ◇P — liveness under weak fairness: P holds eventually on all fair paths from init
    Eventually(Expr),
    /// □(P => ◇Q) — response / progress under weak fairness: whenever P holds, Q eventually holds
    LeadsTo(Expr, Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct NamedTemporal {
    pub name: String,
    pub formula: TemporalFormula,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GuardedTransition {
    pub guard: Expr,
    pub updates: Vec<(String, Expr)>,
}

/// `clock <name> period <n><unit>`: the controller's scan period, in microseconds.
#[derive(Debug, Clone, PartialEq)]
pub struct ClockDecl {
    pub name: String,
    pub period_us: i64,
    pub span: Span,
}

/// `deadline <name>: <latch> => <response> within <n><unit> [in <phase>]`: once `latch`
/// holds (while `phase` holds, default always), `response` must hold within `within_us`.
#[derive(Debug, Clone, PartialEq)]
pub struct DeadlineDecl {
    pub name: String,
    pub latch: Expr,
    pub response: Expr,
    pub within_us: i64,
    pub phase: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SystemDecl {
    pub name: String,
    /// Scan clock (`clock scan period 1ms`); consumed by `timed::lower_program`.
    pub clocks: Vec<ClockDecl>,
    /// Response deadlines; consumed by `timed::lower_program`.
    pub deadlines: Vec<DeadlineDecl>,
    pub states: Vec<StateVarDecl>,
    pub invariants: Vec<NamedInvariant>,
    pub temporals: Vec<NamedTemporal>,
    pub variant: Option<Expr>,
    pub terminal: Option<Expr>,
    pub transitions: Vec<GuardedTransition>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetDecl {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssertDecl {
    pub formula: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeExpr {
    Named(String),
    List(Box<TypeExpr>),
    Map(Box<TypeExpr>, Box<TypeExpr>),
    Fn(Vec<TypeExpr>, Box<TypeExpr>),
}

impl fmt::Display for TypeExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeExpr::Named(n) => write!(f, "{}", n),
            TypeExpr::List(inner) => write!(f, "List<{}>", inner),
            TypeExpr::Map(k, v) => write!(f, "Map<{}, {}>", k, v),
            TypeExpr::Fn(args, ret) => {
                let s: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "({}) -> {}", s.join(", "), ret)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // FOL
    Implies,
    Iff,
    And,
    Or,
    // Comparison
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    In,
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Range
    Range,
    RangeInc,
    // Pipeline
    Pipe,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinOp::Implies => "=>",
            BinOp::Iff => "<=>",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::Eq => "==",
            BinOp::Neq => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::In => "in",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Range => "..",
            BinOp::RangeInc => "..=",
            BinOp::Pipe => "|>",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GuardedBranch {
    pub guard: Expr,
    pub body: GclBody,
}

#[derive(Debug, Clone, PartialEq)]
pub enum GclBody {
    Expr(Expr),
    Updates(Vec<(String, Expr)>),
    Skip,
    Abort,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard,
    Var(String),
    Int(i64),
    Bool(bool),
    Str(String),
    Variant(String, Vec<String>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum QuantifierKind {
    Forall,
    Exists,
    Choose,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Var(String),
    Placeholder, // _

    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    // FOL Quantifier & Nondeterministic Choose: forall x in Domain : Body
    Quantifier {
        kind: QuantifierKind,
        var: String,
        domain: Box<Expr>,
        body: Box<Expr>,
    },

    // Dijkstra Guarded Alternative: if G1 -> E1 [] G2 -> E2 fi
    IfFi {
        branches: Vec<GuardedBranch>,
    },

    // Dijkstra Guarded Loop:
    // do x = init1, y = init2 invariant I variant V : G1 -> x := e1 [] G2 -> y := e2 od then result_expr
    DoOd {
        inits: Vec<(String, Expr)>,
        invariant: Option<Box<Expr>>,
        variant: Option<Box<Expr>>,
        branches: Vec<GuardedBranch>,
        then_expr: Box<Expr>,
    },

    // ADT Match expression
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },

    // Concept / Record construction: Pipeline { id: "P1", pressure: 100 }
    RecordInit {
        concept: String,
        fields: Vec<(String, Expr)>,
    },

    // Functional Record Update: expr with { field: new_val }
    RecordWith {
        base: Box<Expr>,
        updates: Vec<(String, Expr)>,
    },

    // Field access: expr.field
    FieldAccess {
        base: Box<Expr>,
        field: String,
    },

    // Function or Variant call: f(a, b) or f(_, b)
    Call {
        func: String,
        args: Vec<Expr>,
    },

    // List literal: [e1, e2, ...]
    List(Vec<Expr>),

    // Let-in expression: let x = e1 in e2
    LetIn {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },
}
