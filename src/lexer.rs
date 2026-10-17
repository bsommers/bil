use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub line: usize,
    pub col: usize,
}

impl Span {
    pub fn new(line: usize, col: usize) -> Self {
        Self { line, col }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpannedToken {
    pub token: Token,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals & Identifiers
    Ident(String),
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),

    // Keywords - Declarations & OntoLogic
    Concept,
    Type,
    Axiom,
    Spec,
    Fn,
    Refines,
    Requires,
    Ensures,
    System,
    State,
    Invariant,
    Variant,
    Transition,
    Terminal,
    Let,
    Assert,
    In,
    With,
    Match,
    Choose,

    // Keywords - Guarded Command Language (Dijkstra)
    If,
    Fi,
    Do,
    Od,
    Then,
    Skip,
    Abort,

    // Keywords - First-Order Logic
    Forall, // forall, ∀
    Exists, // exists, ∃

    // Operators - GCL & Logic & Pipelines
    GuardSep,   // [] or ▯
    Arrow,      // -> or →
    Assign,     // :=
    Implies,    // => or ⇒
    Iff,        // <=> or ⇔
    And,        // && or ∧ or and
    Or,         // || or ∨ or or
    Not,        // ! or ¬ or not
    Subconcept, // <: or ⊑
    Pipe,       // |> or ▷
    RangeInc,   // ..=
    Range,      // ..
    Underscore, // _

    // Comparisons
    EqEq, // ==
    Neq,  // != or ≠
    Lt,   // <
    Le,   // <= or ≤
    Gt,   // >
    Ge,   // >= or ≥
    Eq,   // =

    // Arithmetic
    Plus,    // +
    Minus,   // -
    Star,    // *
    Slash,   // /
    Percent, // %

    // Delimiters
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
    Comma,    // ,
    Colon,    // :
    Semi,     // ;
    Dot,      // .
    Bar,      // |

    Eof,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LexError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[LexError at {}] {}", self.span, self.message)
    }
}

pub fn tokenize(input: &str) -> Result<Vec<SpannedToken>, LexError> {
    let mut chars = input.chars().peekable();
    let mut tokens = Vec::new();
    let mut line = 1usize;
    let mut col = 1usize;

    while let Some(&ch) = chars.peek() {
        if ch == '\n' {
            chars.next();
            line += 1;
            col = 1;
            continue;
        }
        if ch.is_whitespace() {
            chars.next();
            col += 1;
            continue;
        }

        let span = Span::new(line, col);

        // Line comments: // or --
        if ch == '/' {
            let mut clone = chars.clone();
            clone.next();
            if clone.peek() == Some(&'/') {
                while let Some(&c) = chars.peek() {
                    if c == '\n' {
                        break;
                    }
                    chars.next();
                    col += 1;
                }
                continue;
            }
        }

        // String literal
        if ch == '"' {
            chars.next();
            col += 1;
            let mut s = String::new();
            let mut closed = false;
            while let Some(c) = chars.next() {
                col += 1;
                if c == '"' {
                    closed = true;
                    break;
                } else if c == '\\' {
                    if let Some(esc) = chars.next() {
                        col += 1;
                        match esc {
                            'n' => s.push('\n'),
                            't' => s.push('\t'),
                            '"' => s.push('"'),
                            '\\' => s.push('\\'),
                            other => s.push(other),
                        }
                    }
                } else {
                    if c == '\n' {
                        line += 1;
                        col = 1;
                    }
                    s.push(c);
                }
            }
            if !closed {
                return Err(LexError {
                    message: "Unterminated string literal".into(),
                    span,
                });
            }
            tokens.push(SpannedToken {
                token: Token::Str(s),
                span,
            });
            continue;
        }

        // Numbers
        if ch.is_ascii_digit() {
            let mut num_str = String::new();
            let mut is_float = false;
            while let Some(&c) = chars.peek() {
                if c.is_ascii_digit() {
                    num_str.push(c);
                    chars.next();
                    col += 1;
                } else if c == '.' && !is_float {
                    // Check not '..' range
                    let mut clone = chars.clone();
                    clone.next();
                    if let Some(&next_c) = clone.peek() {
                        if next_c.is_ascii_digit() {
                            is_float = true;
                            num_str.push('.');
                            chars.next();
                            col += 1;
                            continue;
                        }
                    }
                    break;
                } else {
                    break;
                }
            }
            if is_float {
                let val = num_str.parse::<f64>().map_err(|_| LexError {
                    message: format!("Invalid float literal: {}", num_str),
                    span,
                })?;
                tokens.push(SpannedToken {
                    token: Token::Float(val),
                    span,
                });
            } else {
                let val = num_str.parse::<i64>().map_err(|_| LexError {
                    message: format!("Invalid int literal: {}", num_str),
                    span,
                })?;
                tokens.push(SpannedToken {
                    token: Token::Int(val),
                    span,
                });
            }
            continue;
        }

        // Identifiers & Keywords
        if ch.is_alphabetic() || ch == '_' {
            let mut ident = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_alphanumeric() || c == '_' {
                    ident.push(c);
                    chars.next();
                    col += 1;
                } else {
                    break;
                }
            }
            let token = match ident.as_str() {
                "_" => Token::Underscore,
                "true" | "True" => Token::Bool(true),
                "false" | "False" => Token::Bool(false),
                "concept" => Token::Concept,
                "type" => Token::Type,
                "axiom" => Token::Axiom,
                "spec" => Token::Spec,
                "fn" => Token::Fn,
                "refines" => Token::Refines,
                "requires" => Token::Requires,
                "ensures" => Token::Ensures,
                "system" => Token::System,
                "state" => Token::State,
                "invariant" => Token::Invariant,
                "variant" => Token::Variant,
                "transition" => Token::Transition,
                "terminal" => Token::Terminal,
                "let" => Token::Let,
                "assert" => Token::Assert,
                "in" => Token::In,
                "with" => Token::With,
                "match" => Token::Match,
                "choose" => Token::Choose,
                "if" => Token::If,
                "fi" => Token::Fi,
                "do" => Token::Do,
                "od" => Token::Od,
                "then" => Token::Then,
                "skip" => Token::Skip,
                "abort" => Token::Abort,
                "forall" => Token::Forall,
                "exists" => Token::Exists,
                "and" => Token::And,
                "or" => Token::Or,
                "not" => Token::Not,
                "implies" => Token::Implies,
                "iff" => Token::Iff,
                _ => Token::Ident(ident),
            };
            tokens.push(SpannedToken { token, span });
            continue;
        }

        // Unicode mathematical & logical operators
        match ch {
            '∀' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Forall,
                    span,
                });
                continue;
            }
            '∃' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Exists,
                    span,
                });
                continue;
            }
            '∈' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::In,
                    span,
                });
                continue;
            }
            '⇒' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Implies,
                    span,
                });
                continue;
            }
            '⇔' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Iff,
                    span,
                });
                continue;
            }
            '∧' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::And,
                    span,
                });
                continue;
            }
            '∨' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Or,
                    span,
                });
                continue;
            }
            '¬' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Not,
                    span,
                });
                continue;
            }
            '▯' | '□' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::GuardSep,
                    span,
                });
                continue;
            }
            '→' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Arrow,
                    span,
                });
                continue;
            }
            '⊑' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Subconcept,
                    span,
                });
                continue;
            }
            '▷' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Pipe,
                    span,
                });
                continue;
            }
            '≤' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Le,
                    span,
                });
                continue;
            }
            '≥' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Ge,
                    span,
                });
                continue;
            }
            '≠' => {
                chars.next();
                col += 1;
                tokens.push(SpannedToken {
                    token: Token::Neq,
                    span,
                });
                continue;
            }
            _ => {}
        }

        // Multi-char & single-char ASCII operators
        chars.next();
        col += 1;
        let next_ch = chars.peek().copied();

        let token = match (ch, next_ch) {
            ('[', Some(']')) => {
                chars.next();
                col += 1;
                Token::GuardSep
            }
            ('[', _) => Token::LBracket,
            (']', _) => Token::RBracket,
            ('-', Some('>')) => {
                chars.next();
                col += 1;
                Token::Arrow
            }
            ('-', _) => Token::Minus,
            (':', Some('=')) => {
                chars.next();
                col += 1;
                Token::Assign
            }
            (':', _) => Token::Colon,
            ('=', Some('>')) => {
                chars.next();
                col += 1;
                Token::Implies
            }
            ('=', Some('=')) => {
                chars.next();
                col += 1;
                Token::EqEq
            }
            ('=', _) => Token::Eq,
            ('<', Some('=')) => {
                chars.next();
                col += 1;
                if chars.peek() == Some(&'>') {
                    chars.next();
                    col += 1;
                    Token::Iff
                } else {
                    Token::Le
                }
            }
            ('<', Some(':')) => {
                chars.next();
                col += 1;
                Token::Subconcept
            }
            ('<', _) => Token::Lt,
            ('>', Some('=')) => {
                chars.next();
                col += 1;
                Token::Ge
            }
            ('>', _) => Token::Gt,
            ('!', Some('=')) => {
                chars.next();
                col += 1;
                Token::Neq
            }
            ('!', _) => Token::Not,
            ('&', Some('&')) => {
                chars.next();
                col += 1;
                Token::And
            }
            ('|', Some('|')) => {
                chars.next();
                col += 1;
                Token::Or
            }
            ('|', Some('>')) => {
                chars.next();
                col += 1;
                Token::Pipe
            }
            ('|', _) => Token::Bar,
            ('.', Some('.')) => {
                chars.next();
                col += 1;
                if chars.peek() == Some(&'=') {
                    chars.next();
                    col += 1;
                    Token::RangeInc
                } else {
                    Token::Range
                }
            }
            ('.', _) => Token::Dot,
            ('+', _) => Token::Plus,
            ('*', _) => Token::Star,
            ('/', _) => Token::Slash,
            ('%', _) => Token::Percent,
            ('(', _) => Token::LParen,
            (')', _) => Token::RParen,
            ('{', _) => Token::LBrace,
            ('}', _) => Token::RBrace,
            (',', _) => Token::Comma,
            (';', _) => Token::Semi,
            _ => {
                return Err(LexError {
                    message: format!("Unexpected character '{}'", ch),
                    span,
                });
            }
        };

        tokens.push(SpannedToken { token, span });
    }

    tokens.push(SpannedToken {
        token: Token::Eof,
        span: Span::new(line, col),
    });
    Ok(tokens)
}
