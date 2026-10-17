//! Unified checked Euclidean integer semantics shared across AST interpreter,
//! Bytecode VM, Native AOT codegen, and SMT-LIB2 `Int` (`div`/`mod`).

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
