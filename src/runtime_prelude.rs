#[derive(Debug, Clone, PartialEq)]
pub enum BilVal {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Unit,
    List(Rc<Vec<BilVal>>),
    Concept {
        name: String,
        fields: BTreeMap<String, BilVal>,
    },
    Adt {
        variant: String,
        fields: Vec<BilVal>,
    },
}

impl fmt::Display for BilVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BilVal::Int(v) => write!(f, "{}", v),
            // Keep the decimal point on whole values (`-3.0`) to match the interpreter.
            BilVal::Float(v) if v.is_finite() && v.fract() == 0.0 => write!(f, "{:.1}", v),
            BilVal::Float(v) => write!(f, "{}", v),
            BilVal::Bool(v) => write!(f, "{}", v),
            BilVal::Str(v) => write!(f, "\"{}\"", v),
            BilVal::Unit => write!(f, "()"),
            BilVal::List(items) => {
                let s: Vec<String> = items.iter().map(|i| i.to_string()).collect();
                write!(f, "[{}]", s.join(", "))
            }
            BilVal::Concept { name, fields } => {
                let s: Vec<String> = fields
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v))
                    .collect();
                write!(f, "{} {{ {} }}", name, s.join(", "))
            }
            BilVal::Adt { variant, fields } => {
                if fields.is_empty() {
                    write!(f, "{}", variant)
                } else {
                    let s: Vec<String> = fields.iter().map(|v| v.to_string()).collect();
                    write!(f, "{}({})", variant, s.join(", "))
                }
            }
        }
    }
}

fn eval_binop(op: &str, l: BilVal, r: BilVal) -> BilVal {
    match op {
        "=>" => match (l, r) {
            (BilVal::Bool(a), BilVal::Bool(b)) => BilVal::Bool(!a || b),
            _ => panic!("=>"),
        },
        "<=>" => match (l, r) {
            (BilVal::Bool(a), BilVal::Bool(b)) => BilVal::Bool(a == b),
            _ => panic!("<=>"),
        },
        "&&" => match (l, r) {
            (BilVal::Bool(a), BilVal::Bool(b)) => BilVal::Bool(a && b),
            _ => panic!("&&"),
        },
        "||" => match (l, r) {
            (BilVal::Bool(a), BilVal::Bool(b)) => BilVal::Bool(a || b),
            _ => panic!("||"),
        },
        "==" => BilVal::Bool(l == r),
        "!=" => BilVal::Bool(l != r),
        "<" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => BilVal::Bool(a < b),
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Bool(a < b),
            _ => panic!("<"),
        },
        "<=" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => BilVal::Bool(a <= b),
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Bool(a <= b),
            _ => panic!("<="),
        },
        ">" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => BilVal::Bool(a > b),
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Bool(a > b),
            _ => panic!(">"),
        },
        ">=" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => BilVal::Bool(a >= b),
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Bool(a >= b),
            _ => panic!(">="),
        },
        "in" => match (l, r) {
            (elem, BilVal::List(list)) => BilVal::Bool(list.contains(&elem)),
            _ => panic!("in"),
        },
        ".." => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => {
                assert!(
                    !(b > a && (b as i128 - a as i128) > 100_000),
                    "Range {}..{} exceeds maximum materialized length (100000)",
                    a,
                    b
                );
                BilVal::List(Rc::new((a..b).map(BilVal::Int).collect()))
            }
            _ => panic!(".."),
        },
        "..=" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => {
                assert!(
                    !(b >= a && (b as i128 - a as i128 + 1) > 100_000),
                    "Range {}..={} exceeds maximum materialized length (100000)",
                    a,
                    b
                );
                BilVal::List(Rc::new((a..=b).map(BilVal::Int).collect()))
            }
            _ => panic!("..="),
        },
        "+" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => {
                BilVal::Int(a.checked_add(b).expect("Integer addition overflow"))
            }
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Float(a + b),
            (BilVal::Str(a), BilVal::Str(b)) => BilVal::Str(format!("{}{}", a, b)),
            _ => panic!("+"),
        },
        "-" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => {
                BilVal::Int(a.checked_sub(b).expect("Integer subtraction overflow"))
            }
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Float(a - b),
            _ => panic!("-"),
        },
        "*" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => {
                BilVal::Int(a.checked_mul(b).expect("Integer multiplication overflow"))
            }
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Float(a * b),
            _ => panic!("*"),
        },
        "/" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => {
                BilVal::Int(a.checked_div_euclid(b).expect("Division by zero or overflow"))
            }
            (BilVal::Float(a), BilVal::Float(b)) => BilVal::Float(a / b),
            _ => panic!("/"),
        },
        "%" => match (l, r) {
            (BilVal::Int(a), BilVal::Int(b)) => {
                BilVal::Int(a.checked_rem_euclid(b).expect("Modulo by zero or overflow"))
            }
            _ => panic!("%"),
        },
        _ => panic!("unknown op {}", op),
    }
}

static BIL_RNG_STATE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(42);

fn next_rand_index(len: usize) -> usize {
    if len <= 1 {
        return 0;
    }
    let mut x = BIL_RNG_STATE.load(std::sync::atomic::Ordering::Relaxed);
    if x == 0 {
        x = 0x9E3779B97F4A7C15;
    }
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    BIL_RNG_STATE.store(x, std::sync::atomic::Ordering::Relaxed);
    let r = x.wrapping_mul(0x2545F4914F6CDD1D);
    (r as usize) % len
}

thread_local! {
    static CONCEPT_STORE: std::cell::RefCell<BTreeMap<String, Vec<BilVal>>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

fn register_instance(val: &BilVal) {
    match val {
        BilVal::Concept { name, .. } => {
            CONCEPT_STORE.with(|store| {
                let mut map = store.borrow_mut();
                let list = map.entry(name.clone()).or_default();
                if !list.contains(val) {
                    list.push(val.clone());
                }
            });
        }
        BilVal::List(items) => {
            for item in items.iter() {
                register_instance(item);
            }
        }
        _ => {}
    }
}

/// Call-depth and loop-step limits, matching `eval` (`MAX_CALL_DEPTH`) and its `do ... od` bound,
/// so a runaway native program stops with a clean panic instead of overflowing the OS stack or hanging.
pub const MAX_NATIVE_CALL_DEPTH: usize = 64;
pub const MAX_NATIVE_LOOP_STEPS: usize = 100_000;

thread_local! {
    static NATIVE_CALL_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Decrements the call depth when a `bil_fn_*` frame returns (or unwinds).
pub struct CallDepthGuard;

impl Drop for CallDepthGuard {
    fn drop(&mut self) {
        NATIVE_CALL_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

pub fn enter_bil_call(name: &str) -> CallDepthGuard {
    NATIVE_CALL_DEPTH.with(|d| {
        if d.get() >= MAX_NATIVE_CALL_DEPTH {
            panic!(
                "Call stack depth exceeded maximum ({}) calling '{}'",
                MAX_NATIVE_CALL_DEPTH, name
            );
        }
        d.set(d.get() + 1);
    });
    CallDepthGuard
}

/// Counts one executed `do ... od` step; call it after a guard fired.
pub fn bil_loop_step(steps: &mut usize) {
    *steps += 1;
    if *steps > MAX_NATIVE_LOOP_STEPS {
        panic!("GCL 'do ... od' exceeded maximum step bound (100,000)");
    }
}
