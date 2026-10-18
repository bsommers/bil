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
