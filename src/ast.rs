use crate::lexer::Span;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Concept(ConceptDecl),
    TypeDecl(AdtDecl),
    Axiom(AxiomDecl),
    Spec(SpecDecl),
    FnDecl(FnDecl),
    System(SystemDecl),
    Let(LetDecl),
    Assert(AssertDecl),
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
pub struct GuardedTransition {
    pub guard: Expr,
    pub updates: Vec<(String, Expr)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SystemDecl {
    pub name: String,
    pub states: Vec<StateVarDecl>,
    pub invariants: Vec<NamedInvariant>,
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
