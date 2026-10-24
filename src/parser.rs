use crate::ast::*;
use crate::lexer::{Span, SpannedToken, Token};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[ParseError at {}] {}", self.span, self.message)
    }
}

pub const MAX_PARSE_DEPTH: usize = 128;

pub struct Parser {
    tokens: Vec<SpannedToken>,
    pos: usize,
    in_let_value: bool,
    depth: usize,
    /// Span of each finished expression node, in completion (post-order) order.
    /// See `Program::for_each_expr_postorder`.
    node_spans: Vec<Span>,
}

impl Parser {
    pub fn new(tokens: Vec<SpannedToken>) -> Self {
        Self {
            tokens,
            pos: 0,
            in_let_value: false,
            depth: 0,
            node_spans: Vec::new(),
        }
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.pos].token
    }

    fn peek_at(&self, offset: usize) -> &Token {
        let idx = (self.pos + offset).min(self.tokens.len() - 1);
        &self.tokens[idx].token
    }

    /// Records `span` for a just-finished expression node. Children finish before parents,
    /// so spans accumulate in post-order.
    fn node(&mut self, span: Span, expr: Expr) -> Expr {
        self.node_spans.push(span);
        expr
    }

    /// Parses one top-level expression and returns it with the spans its nodes recorded.
    fn parse_root_expr(&mut self) -> Result<(Expr, Vec<Span>), ParseError> {
        let mark = self.node_spans.len();
        let e = self.parse_expr(0)?;
        Ok((e, self.node_spans.split_off(mark)))
    }

    fn span(&self) -> Span {
        self.tokens[self.pos].span
    }

    fn advance(&mut self) -> SpannedToken {
        let tok = self.tokens[self.pos].clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn expect(&mut self, expected: &Token) -> Result<Span, ParseError> {
        if self.peek() == expected {
            Ok(self.advance().span)
        } else {
            Err(ParseError {
                message: format!("Expected {:?}, found {:?}", expected, self.peek()),
                span: self.span(),
            })
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.peek().clone() {
            Token::Ident(name) => {
                self.advance();
                Ok(name)
            }
            other => Err(ParseError {
                message: format!("Expected identifier, found {:?}", other),
                span: self.span(),
            }),
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut items = Vec::new();
        while self.peek() != &Token::Eof {
            items.push(self.parse_item()?);
        }
        Ok(Program {
            items,
            expr_spans: std::mem::take(&mut self.node_spans),
        })
    }

    fn parse_item(&mut self) -> Result<Item, ParseError> {
        match self.peek() {
            Token::Concept => Ok(Item::Concept(self.parse_concept()?)),
            Token::Type => Ok(Item::TypeDecl(self.parse_type_decl()?)),
            Token::Axiom => Ok(Item::Axiom(self.parse_axiom()?)),
            Token::Spec => Ok(Item::Spec(self.parse_spec()?)),
            Token::Proof => Ok(Item::Proof(self.parse_proof()?)),
            Token::Fn => Ok(Item::FnDecl(self.parse_fn()?)),
            Token::System => Ok(Item::System(self.parse_system()?)),
            Token::Let => Ok(Item::Let(self.parse_let()?)),
            Token::Assert => Ok(Item::Assert(self.parse_assert()?)),
            other => Err(ParseError {
                message: format!("Expected top-level declaration, found {:?}", other),
                span: self.span(),
            }),
        }
    }

    fn parse_proof(&mut self) -> Result<ProofDecl, ParseError> {
        let span = self.expect(&Token::Proof)?;
        let name = self.expect_ident()?;
        let params = if self.peek() == &Token::LParen {
            self.parse_params()?
        } else {
            Vec::new()
        };
        let requires = if self.peek() == &Token::Requires {
            self.advance();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        self.expect(&Token::Ensures)?;
        let ensures = self.parse_expr(0)?;
        let body = if self.peek() == &Token::LBrace {
            self.advance();
            let b = self.parse_expr(0)?;
            self.expect(&Token::RBrace)?;
            Some(b)
        } else if self.peek() == &Token::Eq {
            self.advance();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        Ok(ProofDecl {
            name,
            params,
            requires,
            ensures,
            body,
            span,
        })
    }

    fn parse_concept(&mut self) -> Result<ConceptDecl, ParseError> {
        let span = self.expect(&Token::Concept)?;
        let name = self.expect_ident()?;
        let parent = if self.peek() == &Token::Subconcept {
            self.advance();
            Some(self.expect_ident()?)
        } else {
            None
        };
        let mut fields = Vec::new();
        if self.peek() == &Token::LBrace {
            self.advance();
            while self.peek() != &Token::RBrace && self.peek() != &Token::Eof {
                let fname = self.expect_ident()?;
                self.expect(&Token::Colon)?;
                let ty = self.parse_type_expr()?;
                fields.push(FieldDecl { name: fname, ty });
                if self.peek() == &Token::Comma {
                    self.advance();
                }
            }
            self.expect(&Token::RBrace)?;
        }
        Ok(ConceptDecl {
            name,
            parent,
            fields,
            span,
        })
    }

    fn parse_type_decl(&mut self) -> Result<AdtDecl, ParseError> {
        let span = self.expect(&Token::Type)?;
        let name = self.expect_ident()?;
        self.expect(&Token::Eq)?;
        if self.peek() == &Token::Bar {
            self.advance();
        }
        let mut variants = Vec::new();
        loop {
            let vname = self.expect_ident()?;
            let mut payload = Vec::new();
            if self.peek() == &Token::LParen {
                self.advance();
                while self.peek() != &Token::RParen && self.peek() != &Token::Eof {
                    payload.push(self.parse_type_expr()?);
                    if self.peek() == &Token::Comma {
                        self.advance();
                    }
                }
                self.expect(&Token::RParen)?;
            }
            variants.push(VariantDecl {
                name: vname,
                payload,
            });
            if self.peek() == &Token::Bar {
                self.advance();
            } else {
                break;
            }
        }
        Ok(AdtDecl {
            name,
            variants,
            span,
        })
    }

    fn parse_axiom(&mut self) -> Result<AxiomDecl, ParseError> {
        let span = self.expect(&Token::Axiom)?;
        let name = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let formula = self.parse_expr(0)?;
        Ok(AxiomDecl {
            name,
            formula,
            span,
        })
    }

    fn parse_params(&mut self) -> Result<Vec<Param>, ParseError> {
        self.expect(&Token::LParen)?;
        let mut params = Vec::new();
        while self.peek() != &Token::RParen && self.peek() != &Token::Eof {
            let name = self.expect_ident()?;
            self.expect(&Token::Colon)?;
            let ty = self.parse_type_expr()?;
            params.push(Param { name, ty });
            if self.peek() == &Token::Comma {
                self.advance();
            }
        }
        self.expect(&Token::RParen)?;
        Ok(params)
    }

    fn parse_spec(&mut self) -> Result<SpecDecl, ParseError> {
        let span = self.expect(&Token::Spec)?;
        let name = self.expect_ident()?;
        let params = self.parse_params()?;
        self.expect(&Token::Arrow)?;
        let ret_ty = self.parse_type_expr()?;
        let requires = if self.peek() == &Token::Requires {
            self.advance();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        let ensures = if self.peek() == &Token::Ensures {
            self.advance();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        Ok(SpecDecl {
            name,
            params,
            ret_ty,
            requires,
            ensures,
            span,
        })
    }

    fn parse_fn(&mut self) -> Result<FnDecl, ParseError> {
        let span = self.expect(&Token::Fn)?;
        let name = self.expect_ident()?;
        let params = self.parse_params()?;
        self.expect(&Token::Arrow)?;
        let ret_ty = self.parse_type_expr()?;
        let refines = if self.peek() == &Token::Refines || self.peek() == &Token::Subconcept {
            self.advance();
            Some(self.expect_ident()?)
        } else {
            None
        };
        let requires = if self.peek() == &Token::Requires {
            self.advance();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        let ensures = if self.peek() == &Token::Ensures {
            self.advance();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        let variant = if self.peek() == &Token::Variant {
            self.advance();
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        self.expect(&Token::Eq)?;
        let body = self.parse_expr(0)?;
        Ok(FnDecl {
            name,
            params,
            ret_ty,
            refines,
            requires,
            ensures,
            variant,
            body,
            span,
        })
    }

    fn parse_system(&mut self) -> Result<SystemDecl, ParseError> {
        let span = self.expect(&Token::System)?;
        let name = self.expect_ident()?;
        self.expect(&Token::LBrace)?;

        let mut states = Vec::new();
        let mut invariants = Vec::new();
        let mut temporals = Vec::new();
        let mut variant = None;
        let mut terminal = None;
        let mut transitions = Vec::new();
        // Members are parsed in source order but stored grouped by kind, so collect each
        // group's expression spans separately and lay them out in field order at the end
        // (see `Program::for_each_expr_postorder`).
        let base = self.node_spans.len();
        let (mut state_sp, mut inv_sp, mut temp_sp) = (Vec::new(), Vec::new(), Vec::new());
        let (mut variant_sp, mut terminal_sp, mut trans_sp) = (Vec::new(), Vec::new(), Vec::new());

        while self.peek() != &Token::RBrace && self.peek() != &Token::Eof {
            match self.peek() {
                Token::State => {
                    self.advance();
                    let sname = self.expect_ident()?;
                    self.expect(&Token::Colon)?;
                    let ty = self.parse_type_expr()?;
                    self.expect(&Token::Eq)?;
                    let (init, sp) = self.parse_root_expr()?;
                    state_sp.extend(sp);
                    states.push(StateVarDecl {
                        name: sname,
                        ty,
                        init,
                    });
                }
                Token::Invariant => {
                    self.advance();
                    let iname = self.expect_ident()?;
                    self.expect(&Token::Colon)?;
                    let (formula, sp) = self.parse_root_expr()?;
                    inv_sp.extend(sp);
                    invariants.push(NamedInvariant {
                        name: iname,
                        formula,
                    });
                }
                Token::Temporal => {
                    self.advance();
                    let tname = self.expect_ident()?;
                    self.expect(&Token::Colon)?;
                    let mark = self.node_spans.len();
                    let formula = self.parse_temporal_formula()?;
                    temp_sp.extend(self.node_spans.split_off(mark));
                    temporals.push(NamedTemporal {
                        name: tname,
                        formula,
                    });
                }
                Token::Variant => {
                    self.advance();
                    if self.peek() == &Token::Colon {
                        self.advance();
                    }
                    let (e, sp) = self.parse_root_expr()?;
                    variant = Some(e);
                    variant_sp = sp; // a later `variant` replaces an earlier one
                }
                Token::Terminal => {
                    self.advance();
                    if self.peek() == &Token::Colon {
                        self.advance();
                    }
                    let (e, sp) = self.parse_root_expr()?;
                    terminal = Some(e);
                    terminal_sp = sp;
                }
                Token::Transition => {
                    self.advance();
                    if self.peek() == &Token::Colon {
                        self.advance();
                    }
                    if self.peek() == &Token::GuardSep {
                        self.advance();
                    }
                    loop {
                        let mark = self.node_spans.len();
                        let guard = self.parse_expr(0)?;
                        self.expect(&Token::Arrow)?;
                        let updates = self.parse_updates()?;
                        trans_sp.extend(self.node_spans.split_off(mark));
                        transitions.push(GuardedTransition { guard, updates });
                        if self.peek() == &Token::GuardSep {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                other => {
                    return Err(ParseError {
                        message: format!("Unexpected token in system block: {:?}", other),
                        span: self.span(),
                    });
                }
            }
        }

        self.expect(&Token::RBrace)?;
        self.node_spans.truncate(base);
        for group in [state_sp, inv_sp, temp_sp, variant_sp, terminal_sp, trans_sp] {
            self.node_spans.extend(group);
        }
        Ok(SystemDecl {
            name,
            states,
            invariants,
            temporals,
            variant,
            terminal,
            transitions,
            span,
        })
    }

    fn parse_temporal_formula(&mut self) -> Result<TemporalFormula, ParseError> {
        if let Token::Ident(kw) = self.peek().clone() {
            if kw == "always" && self.peek_at(1) == &Token::LParen {
                self.advance();
                self.expect(&Token::LParen)?;
                let e = self.parse_expr(0)?;
                self.expect(&Token::RParen)?;
                return Ok(TemporalFormula::Always(e));
            }
            if kw == "eventually" && self.peek_at(1) == &Token::LParen {
                self.advance();
                self.expect(&Token::LParen)?;
                let e = self.parse_expr(0)?;
                self.expect(&Token::RParen)?;
                return Ok(TemporalFormula::Eventually(e));
            }
        }
        if self.peek() == &Token::LeadsTo && self.peek_at(1) == &Token::LParen {
            self.advance();
            self.expect(&Token::LParen)?;
            let p = self.parse_expr(0)?;
            self.expect(&Token::Comma)?;
            let q = self.parse_expr(0)?;
            self.expect(&Token::RParen)?;
            return Ok(TemporalFormula::LeadsTo(p, q));
        }

        let lhs = self.parse_expr(0)?;
        if self.peek() == &Token::LeadsTo {
            self.advance();
            let rhs = self.parse_expr(0)?;
            Ok(TemporalFormula::LeadsTo(lhs, rhs))
        } else {
            Ok(TemporalFormula::Always(lhs))
        }
    }

    fn parse_updates(&mut self) -> Result<Vec<(String, Expr)>, ParseError> {
        let mut updates = Vec::new();
        loop {
            let var = self.expect_ident()?;
            self.expect(&Token::Assign)?;
            let expr = self.parse_expr(0)?;
            updates.push((var, expr));
            if self.peek() == &Token::Comma {
                self.advance();
            } else {
                break;
            }
        }
        Ok(updates)
    }

    fn parse_let(&mut self) -> Result<LetDecl, ParseError> {
        let span = self.expect(&Token::Let)?;
        let name = self.expect_ident()?;
        let ty = if self.peek() == &Token::Colon {
            self.advance();
            Some(self.parse_type_expr()?)
        } else {
            None
        };
        self.expect(&Token::Eq)?;
        let value = self.parse_expr(0)?;
        Ok(LetDecl {
            name,
            ty,
            value,
            span,
        })
    }

    fn parse_assert(&mut self) -> Result<AssertDecl, ParseError> {
        let span = self.expect(&Token::Assert)?;
        let formula = self.parse_expr(0)?;
        Ok(AssertDecl { formula, span })
    }

    fn parse_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
        let name = self.expect_ident()?;
        if name == "List" && self.peek() == &Token::Lt {
            self.advance();
            let inner = self.parse_type_expr()?;
            self.expect(&Token::Gt)?;
            Ok(TypeExpr::List(Box::new(inner)))
        } else if name == "Map" && self.peek() == &Token::Lt {
            self.advance();
            let k = self.parse_type_expr()?;
            self.expect(&Token::Comma)?;
            let v = self.parse_type_expr()?;
            self.expect(&Token::Gt)?;
            Ok(TypeExpr::Map(Box::new(k), Box::new(v)))
        } else {
            Ok(TypeExpr::Named(name))
        }
    }

    // Pratt parser for expressions with bounded recursion depth
    pub fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        if self.depth >= MAX_PARSE_DEPTH {
            return Err(ParseError {
                message: format!(
                    "Expression nesting depth exceeded maximum ({})",
                    MAX_PARSE_DEPTH
                ),
                span: self.span(),
            });
        }
        self.depth += 1;
        let res = self.parse_expr_inner(min_bp);
        self.depth -= 1;
        res
    }

    fn parse_expr_inner(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_prefix()?;

        loop {
            // Postfix operators: field access `.field` and record update `with { ... }`
            if self.peek() == &Token::Dot {
                if 20 < min_bp {
                    break;
                }
                let dot = self.advance().span;
                let field = self.expect_ident()?;
                lhs = self.node(
                    dot,
                    Expr::FieldAccess {
                        base: Box::new(lhs),
                        field,
                    },
                );
                continue;
            }
            if self.peek() == &Token::With {
                if 18 < min_bp {
                    break;
                }
                let with = self.advance().span;
                self.expect(&Token::LBrace)?;
                let mut updates = Vec::new();
                while self.peek() != &Token::RBrace && self.peek() != &Token::Eof {
                    let fname = self.expect_ident()?;
                    self.expect(&Token::Colon)?;
                    let val = self.parse_expr(0)?;
                    updates.push((fname, val));
                    if self.peek() == &Token::Comma {
                        self.advance();
                    }
                }
                self.expect(&Token::RBrace)?;
                lhs = self.node(
                    with,
                    Expr::RecordWith {
                        base: Box::new(lhs),
                        updates,
                    },
                );
                continue;
            }

            let op = match self.peek() {
                Token::Pipe => BinOp::Pipe,
                Token::Iff => BinOp::Iff,
                Token::Implies => BinOp::Implies,
                Token::Or => BinOp::Or,
                Token::And => BinOp::And,
                Token::EqEq => BinOp::Eq,
                Token::Neq => BinOp::Neq,
                Token::Lt => BinOp::Lt,
                Token::Le => BinOp::Le,
                Token::Gt => BinOp::Gt,
                Token::Ge => BinOp::Ge,
                Token::In if !self.in_let_value => BinOp::In,
                Token::Range => BinOp::Range,
                Token::RangeInc => BinOp::RangeInc,
                Token::Plus => BinOp::Add,
                Token::Minus => BinOp::Sub,
                Token::Star => BinOp::Mul,
                Token::Slash => BinOp::Div,
                Token::Percent => BinOp::Mod,
                _ => break,
            };

            let (l_bp, r_bp) = infix_binding_power(op);
            if l_bp < min_bp {
                break;
            }
            let op_span = self.advance().span;
            let rhs = self.parse_expr(r_bp)?;
            lhs = self.node(
                op_span,
                Expr::Binary {
                    op,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                },
            );
        }

        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> Result<Expr, ParseError> {
        let start = self.span();
        match self.peek().clone() {
            Token::Int(v) => {
                self.advance();
                Ok(self.node(start, Expr::Int(v)))
            }
            Token::Float(v) => {
                self.advance();
                Ok(self.node(start, Expr::Float(v)))
            }
            Token::Bool(v) => {
                self.advance();
                Ok(self.node(start, Expr::Bool(v)))
            }
            Token::Str(v) => {
                self.advance();
                Ok(self.node(start, Expr::Str(v)))
            }
            Token::Underscore => {
                self.advance();
                Ok(self.node(start, Expr::Placeholder))
            }
            Token::Not => {
                self.advance();
                let expr = self.parse_expr(17)?;
                Ok(self.node(
                    start,
                    Expr::Unary {
                        op: UnaryOp::Not,
                        expr: Box::new(expr),
                    },
                ))
            }
            Token::Minus => {
                self.advance();
                let expr = self.parse_expr(17)?;
                Ok(self.node(
                    start,
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        expr: Box::new(expr),
                    },
                ))
            }
            Token::LParen => {
                self.advance();
                let saved = self.in_let_value;
                self.in_let_value = false;
                let expr = self.parse_expr(0);
                self.in_let_value = saved;
                let expr = expr?;
                self.expect(&Token::RParen)?;
                Ok(expr)
            }
            Token::LBracket => {
                self.advance();
                let saved = self.in_let_value;
                self.in_let_value = false;
                let mut items = Vec::new();
                while self.peek() != &Token::RBracket && self.peek() != &Token::Eof {
                    items.push(self.parse_expr(0)?);
                    if self.peek() == &Token::Comma {
                        self.advance();
                    }
                }
                self.in_let_value = saved;
                self.expect(&Token::RBracket)?;
                Ok(self.node(start, Expr::List(items)))
            }
            Token::Forall | Token::Exists | Token::Choose => {
                let kind = match self.advance().token {
                    Token::Forall => QuantifierKind::Forall,
                    Token::Exists => QuantifierKind::Exists,
                    Token::Choose => QuantifierKind::Choose,
                    _ => unreachable!(),
                };
                let var = self.expect_ident()?;
                self.expect(&Token::In)?;
                let domain = self.parse_expr(5)?;
                self.expect(&Token::Colon)?;
                let body = self.parse_expr(0)?;
                Ok(self.node(
                    start,
                    Expr::Quantifier {
                        kind,
                        var,
                        domain: Box::new(domain),
                        body: Box::new(body),
                    },
                ))
            }
            Token::If => self.parse_if_fi(),
            Token::Do => self.parse_do_od(),
            Token::Match => self.parse_match(),
            Token::Let => {
                self.advance();
                let name = self.expect_ident()?;
                self.expect(&Token::Eq)?;
                let saved = self.in_let_value;
                self.in_let_value = true;
                let value = self.parse_expr(0);
                self.in_let_value = saved;
                let value = value?;
                self.expect(&Token::In)?;
                let body = self.parse_expr(0)?;
                Ok(self.node(
                    start,
                    Expr::LetIn {
                        name,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                ))
            }
            Token::Ident(name) => {
                self.advance();
                // Function call: name(args...)
                if self.peek() == &Token::LParen {
                    self.advance();
                    let mut args = Vec::new();
                    while self.peek() != &Token::RParen && self.peek() != &Token::Eof {
                        args.push(self.parse_expr(0)?);
                        if self.peek() == &Token::Comma {
                            self.advance();
                        }
                    }
                    self.expect(&Token::RParen)?;
                    Ok(self.node(start, Expr::Call { func: name, args }))
                } else if self.peek() == &Token::LBrace && self.is_record_init() {
                    self.advance();
                    let mut fields = Vec::new();
                    while self.peek() != &Token::RBrace && self.peek() != &Token::Eof {
                        let fname = self.expect_ident()?;
                        self.expect(&Token::Colon)?;
                        let val = self.parse_expr(0)?;
                        fields.push((fname, val));
                        if self.peek() == &Token::Comma {
                            self.advance();
                        }
                    }
                    self.expect(&Token::RBrace)?;
                    Ok(self.node(
                        start,
                        Expr::RecordInit {
                            concept: name,
                            fields,
                        },
                    ))
                } else {
                    Ok(self.node(start, Expr::Var(name)))
                }
            }
            other => Err(ParseError {
                message: format!("Unexpected token in expression: {:?}", other),
                span: self.span(),
            }),
        }
    }

    fn is_record_init(&self) -> bool {
        // Check `{ ident : ... }` or `{ }`
        if self.peek() != &Token::LBrace {
            return false;
        }
        matches!(
            (self.peek_at(1), self.peek_at(2)),
            (Token::RBrace, _) | (Token::Ident(_), Token::Colon)
        )
    }

    fn parse_if_fi(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::If)?;
        if self.peek() == &Token::GuardSep {
            self.advance();
        }
        let mut branches = Vec::new();
        loop {
            let guard = self.parse_expr(0)?;
            self.expect(&Token::Arrow)?;
            let body = self.parse_gcl_body()?;
            branches.push(GuardedBranch { guard, body });
            if self.peek() == &Token::GuardSep {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&Token::Fi)?;
        Ok(self.node(start, Expr::IfFi { branches }))
    }

    fn parse_do_od(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::Do)?;
        let mut inits = Vec::new();
        loop {
            let vname = self.expect_ident()?;
            self.expect(&Token::Eq)?;
            let val = self.parse_expr(0)?;
            inits.push((vname, val));
            if self.peek() == &Token::Comma {
                self.advance();
            } else {
                break;
            }
        }

        let invariant = if self.peek() == &Token::Invariant {
            self.advance();
            Some(Box::new(self.parse_expr(0)?))
        } else {
            None
        };

        let variant = if self.peek() == &Token::Variant {
            self.advance();
            Some(Box::new(self.parse_expr(0)?))
        } else {
            None
        };

        if self.peek() == &Token::Colon {
            self.advance();
        }
        if self.peek() == &Token::GuardSep {
            self.advance();
        }

        let mut branches = Vec::new();
        loop {
            let guard = self.parse_expr(0)?;
            self.expect(&Token::Arrow)?;
            let body = self.parse_gcl_body()?;
            branches.push(GuardedBranch { guard, body });
            if self.peek() == &Token::GuardSep {
                self.advance();
            } else {
                break;
            }
        }

        let od = self.expect(&Token::Od)?;
        let then_expr = if self.peek() == &Token::Then {
            self.advance();
            Box::new(self.parse_expr(0)?)
        } else {
            // No `then`: the loop yields its first variable, spanned at `od`.
            Box::new(self.node(od, Expr::Var(inits[0].0.clone())))
        };

        Ok(self.node(
            start,
            Expr::DoOd {
                inits,
                invariant,
                variant,
                branches,
                then_expr,
            },
        ))
    }

    fn parse_gcl_body(&mut self) -> Result<GclBody, ParseError> {
        if self.peek() == &Token::Skip {
            self.advance();
            return Ok(GclBody::Skip);
        }
        if self.peek() == &Token::Abort {
            self.advance();
            return Ok(GclBody::Abort);
        }
        // Check if assignment `ident := expr`
        if let (Token::Ident(_), Token::Assign) = (self.peek(), self.peek_at(1)) {
            let updates = self.parse_updates()?;
            return Ok(GclBody::Updates(updates));
        }
        let expr = self.parse_expr(0)?;
        Ok(GclBody::Expr(expr))
    }

    fn parse_match(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&Token::Match)?;
        let scrutinee = self.parse_expr(0)?;
        self.expect(&Token::LBrace)?;
        if self.peek() == &Token::Bar {
            self.advance();
        }
        let mut arms = Vec::new();
        while self.peek() != &Token::RBrace && self.peek() != &Token::Eof {
            let pattern = self.parse_pattern()?;
            self.expect(&Token::Arrow)?;
            let body = self.parse_expr(0)?;
            arms.push(MatchArm { pattern, body });
            if self.peek() == &Token::Comma || self.peek() == &Token::Bar {
                self.advance();
            }
        }
        self.expect(&Token::RBrace)?;
        Ok(self.node(
            start,
            Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms,
            },
        ))
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        match self.peek().clone() {
            Token::Underscore => {
                self.advance();
                Ok(Pattern::Wildcard)
            }
            Token::Int(v) => {
                self.advance();
                Ok(Pattern::Int(v))
            }
            Token::Bool(v) => {
                self.advance();
                Ok(Pattern::Bool(v))
            }
            Token::Str(v) => {
                self.advance();
                Ok(Pattern::Str(v))
            }
            Token::Ident(name) => {
                self.advance();
                if self.peek() == &Token::LParen {
                    self.advance();
                    let mut bindings = Vec::new();
                    while self.peek() != &Token::RParen && self.peek() != &Token::Eof {
                        if self.peek() == &Token::Underscore {
                            self.advance();
                            bindings.push("_".to_string());
                        } else {
                            bindings.push(self.expect_ident()?);
                        }
                        if self.peek() == &Token::Comma {
                            self.advance();
                        }
                    }
                    self.expect(&Token::RParen)?;
                    Ok(Pattern::Variant(name, bindings))
                } else if name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                    Ok(Pattern::Variant(name, vec![]))
                } else {
                    Ok(Pattern::Var(name))
                }
            }
            other => Err(ParseError {
                message: format!("Invalid pattern token: {:?}", other),
                span: self.span(),
            }),
        }
    }
}

fn infix_binding_power(op: BinOp) -> (u8, u8) {
    match op {
        BinOp::Pipe => (1, 2),
        BinOp::Iff => (3, 4),
        BinOp::Implies => (6, 5), // right-associative
        BinOp::Or => (7, 8),
        BinOp::And => (9, 10),
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::In => {
            (11, 12)
        }
        BinOp::Range | BinOp::RangeInc => (13, 14),
        BinOp::Add | BinOp::Sub => (15, 16),
        BinOp::Mul | BinOp::Div | BinOp::Mod => (17, 18),
    }
}
