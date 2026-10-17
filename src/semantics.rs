//! Unified checked Euclidean integer semantics shared across AST interpreter,
//! Bytecode VM, Native AOT codegen, and SMT-LIB2 `Int` (`div`/`mod`).

use crate::ast::{BinOp, Pattern, UnaryOp};
use crate::eval::Value;
use std::rc::Rc;

#[inline]
pub fn int_add(a: i64, b: i64) -> Result<i64, String> {
    a.checked_add(b)
        .ok_or_else(|| format!("Integer addition overflow: {} + {}", a, b))
}

#[inline]
pub fn int_sub(a: i64, b: i64) -> Result<i64, String> {
    a.checked_sub(b)
        .ok_or_else(|| format!("Integer subtraction overflow: {} - {}", a, b))
}

#[inline]
pub fn int_mul(a: i64, b: i64) -> Result<i64, String> {
    a.checked_mul(b)
        .ok_or_else(|| format!("Integer multiplication overflow: {} * {}", a, b))
}

#[inline]
pub fn int_div(a: i64, b: i64) -> Result<i64, String> {
    if b == 0 {
        return Err("Division by zero".into());
    }
    a.checked_div_euclid(b)
        .ok_or_else(|| format!("Integer division overflow: {} / {}", a, b))
}

#[inline]
pub fn int_mod(a: i64, b: i64) -> Result<i64, String> {
    if b == 0 {
        return Err("Modulo by zero".into());
    }
    a.checked_rem_euclid(b)
        .ok_or_else(|| format!("Integer modulo overflow: {} % {}", a, b))
}

#[inline]
pub fn int_neg(a: i64) -> Result<i64, String> {
    a.checked_neg()
        .ok_or_else(|| format!("Integer negation overflow: -{}", a))
}

#[inline]
pub fn int_abs(a: i64) -> Result<i64, String> {
    a.checked_abs()
        .ok_or_else(|| format!("Integer abs overflow: abs({})", a))
}

/// Unified unary operator evaluation shared across AST interpreter and Bytecode VM.
pub fn eval_unary_value(op: UnaryOp, val: Value) -> Result<Value, String> {
    match (op, val) {
        (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
        (UnaryOp::Neg, Value::Int(i)) => int_neg(i).map(Value::Int),
        (UnaryOp::Neg, Value::Float(f)) => Ok(Value::Float(-f)),
        (_, other) => Err(format!("Invalid unary operation on {}", other)),
    }
}

/// Unified binary operator evaluation shared across AST interpreter and Bytecode VM.
pub fn eval_binary_value(op: BinOp, left: Value, right: Value) -> Result<Value, String> {
    match (op, left, right) {
        (BinOp::Implies, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(!a || b)),
        (BinOp::Iff, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
        (BinOp::And, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a && b)),
        (BinOp::Or, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a || b)),
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
            if b > a && (b as i128 - a as i128) > 100_000 {
                return Err(format!(
                    "Range {}..{} exceeds maximum materialized length (100000)",
                    a, b
                ));
            }
            Ok(Value::List(Rc::new((a..b).map(Value::Int).collect())))
        }
        (BinOp::RangeInc, Value::Int(a), Value::Int(b)) => {
            if b >= a && (b as i128 - a as i128 + 1) > 100_000 {
                return Err(format!(
                    "Range {}..={} exceeds maximum materialized length (100000)",
                    a, b
                ));
            }
            Ok(Value::List(Rc::new((a..=b).map(Value::Int).collect())))
        }
        (BinOp::Add, Value::Int(a), Value::Int(b)) => int_add(a, b).map(Value::Int),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => int_sub(a, b).map(Value::Int),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => int_mul(a, b).map(Value::Int),
        (BinOp::Div, Value::Int(a), Value::Int(b)) => int_div(a, b).map(Value::Int),
        (BinOp::Mod, Value::Int(a), Value::Int(b)) => int_mod(a, b).map(Value::Int),
        (BinOp::Add, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
        (BinOp::Div, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{}{}", a, b))),
        (op, l, r) => Err(format!("Unsupported binary op {} on {} and {}", op, l, r)),
    }
}

/// Unified pattern-matching helper shared across AST interpreter and Bytecode VM.
pub fn match_pattern_bindings(pat: &Pattern, val: &Value) -> Option<Vec<(String, Value)>> {
    match (pat, val) {
        (Pattern::Wildcard, _) => Some(vec![]),
        (Pattern::Var(v), other) => Some(vec![(v.clone(), other.clone())]),
        (Pattern::Int(a), Value::Int(b)) if a == b => Some(vec![]),
        (Pattern::Bool(a), Value::Bool(b)) if a == b => Some(vec![]),
        (Pattern::Str(a), Value::Str(b)) if a == b => Some(vec![]),
        (Pattern::Variant(vname, bindings), Value::AdtVariant { variant, fields })
            if vname == variant && bindings.len() == fields.len() =>
        {
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

