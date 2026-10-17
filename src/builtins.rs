//! Centralized registry of BIL builtin functions and pipeline stage operators.
//! Eliminates string-matched builtin tables across `types`, `eval`, `vm`, and `smt`.

use crate::ast::Expr;
use crate::eval::Value;
use crate::ontology::OntologyRegistry;
use crate::semantics;
use crate::smt::sanitize_smt_ident;
use crate::types::Type;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinFn {
    Min,
    Max,
    Abs,
    Count,
    Sum,
    IsA,
}

impl BuiltinFn {
    pub const ALL: &'static [BuiltinFn] = &[
        BuiltinFn::Min,
        BuiltinFn::Max,
        BuiltinFn::Abs,
        BuiltinFn::Count,
        BuiltinFn::Sum,
        BuiltinFn::IsA,
    ];

    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "min" => Some(BuiltinFn::Min),
            "max" => Some(BuiltinFn::Max),
            "abs" => Some(BuiltinFn::Abs),
            "count" => Some(BuiltinFn::Count),
            "sum" => Some(BuiltinFn::Sum),
            "is_a" => Some(BuiltinFn::IsA),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            BuiltinFn::Min => "min",
            BuiltinFn::Max => "max",
            BuiltinFn::Abs => "abs",
            BuiltinFn::Count => "count",
            BuiltinFn::Sum => "sum",
            BuiltinFn::IsA => "is_a",
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            BuiltinFn::Abs | BuiltinFn::Count | BuiltinFn::Sum => 1,
            BuiltinFn::Min | BuiltinFn::Max | BuiltinFn::IsA => 2,
        }
    }

    /// Returns a fixed monomorphic signature `(param_types, ret_type)` for builtins
    /// that can be pre-populated directly into `TypeEnv::bindings`.
    pub fn monomorphic_signature(&self) -> Option<(Vec<Type>, Type)> {
        match self {
            BuiltinFn::Min | BuiltinFn::Max => {
                Some((vec![Type::Int, Type::Int], Type::Int))
            }
            BuiltinFn::Abs => Some((vec![Type::Int], Type::Int)),
            BuiltinFn::Sum => Some((vec![Type::List(Box::new(Type::Int))], Type::Int)),
            // `count` (`List<T> -> Int`) and `is_a` (`(C, String) -> Bool`) are polymorphic
            BuiltinFn::Count | BuiltinFn::IsA => None,
        }
    }

    /// Evaluates a builtin function call with uniform checked arithmetic and ontology semantics.
    pub fn eval(&self, args: &[Value], ontology: &OntologyRegistry) -> Result<Value, String> {
        if args.len() != self.arity() {
            return Err(format!(
                "'{}' expects {} arguments, got {}",
                self.as_str(),
                self.arity(),
                args.len()
            ));
        }
        match self {
            BuiltinFn::Min => match (&args[0], &args[1]) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int((*a).min(*b))),
                _ => Err("min expects two Ints".into()),
            },
            BuiltinFn::Max => match (&args[0], &args[1]) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int((*a).max(*b))),
                _ => Err("max expects two Ints".into()),
            },
            BuiltinFn::Abs => match &args[0] {
                Value::Int(a) => semantics::int_abs(*a).map(Value::Int),
                _ => Err("abs expects an Int".into()),
            },
            BuiltinFn::Count => match &args[0] {
                Value::List(items) => Ok(Value::Int(items.len() as i64)),
                _ => Err("count expects a List".into()),
            },
            BuiltinFn::Sum => match &args[0] {
                Value::List(items) => {
                    let mut total = 0i64;
                    for item in items.iter() {
                        if let Value::Int(v) = item {
                            total = semantics::int_add(total, *v)?;
                        }
                    }
                    Ok(Value::Int(total))
                }
                _ => Err("sum expects List<Int>".into()),
            },
            BuiltinFn::IsA => match (&args[0], &args[1]) {
                (Value::ConceptInstance { concept, .. }, Value::Str(target)) => {
                    Ok(Value::Bool(ontology.is_subconcept(concept, target)))
                }
                _ => Ok(Value::Bool(false)),
            },
        }
    }

    /// Lowers a builtin call to SMT-LIB2 if supported in the first-order theory fragment.
    pub fn to_smt(&self, smt_args: &[String], raw_args: &[Expr]) -> Option<String> {
        if raw_args.len() != self.arity() {
            return None;
        }
        match self {
            BuiltinFn::Abs => Some(format!("(abs {})", smt_args.first()?)),
            BuiltinFn::Min => {
                let a = smt_args.first()?;
                let b = smt_args.get(1)?;
                Some(format!("(ite (<= {} {}) {} {})", a, b, a, b))
            }
            BuiltinFn::Max => {
                let a = smt_args.first()?;
                let b = smt_args.get(1)?;
                Some(format!("(ite (>= {} {}) {} {})", a, b, a, b))
            }
            BuiltinFn::IsA => {
                let x = smt_args.first()?;
                if let Expr::Str(cname) = &raw_args[1] {
                    Some(format!("(is_{} {})", sanitize_smt_ident(cname), x))
                } else {
                    None
                }
            }
            BuiltinFn::Count | BuiltinFn::Sum => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PipeStageBuiltin {
    Where,
    Map,
    SortBy,
    All,
    Any,
    Count,
    Sum,
}

impl PipeStageBuiltin {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "where" | "filter" => Some(PipeStageBuiltin::Where),
            "map" | "select" => Some(PipeStageBuiltin::Map),
            "sort_by" => Some(PipeStageBuiltin::SortBy),
            "all" => Some(PipeStageBuiltin::All),
            "any" => Some(PipeStageBuiltin::Any),
            "count" => Some(PipeStageBuiltin::Count),
            "sum" => Some(PipeStageBuiltin::Sum),
            _ => None,
        }
    }
}
