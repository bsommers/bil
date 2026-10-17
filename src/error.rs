//! Structured diagnostic error hierarchy (`BilError`) preserving source spans across phases.

use crate::eval::RuntimeError;
use crate::lexer::{LexError, Span};
use crate::ontology::OntologyError;
use crate::parser::ParseError;
use crate::types::TypeError;
use std::fmt;

#[derive(Debug, Clone)]
pub enum BilError {
    Lex(LexError),
    Parse(ParseError),
    Ontology(Vec<OntologyError>),
    Type(Vec<TypeError>),
    Runtime(RuntimeError),
    Vm(String),
    Codegen(String),
    ModelCheck(String),
}

impl BilError {
    /// Returns the primary source [`Span`] associated with this error, if available.
    pub fn span(&self) -> Option<Span> {
        match self {
            BilError::Lex(e) => Some(e.span),
            BilError::Parse(e) => Some(e.span),
            BilError::Ontology(errs) => errs.first().map(|e| e.span),
            BilError::Type(errs) => errs.first().map(|e| e.span),
            BilError::Runtime(_)
            | BilError::Vm(_)
            | BilError::Codegen(_)
            | BilError::ModelCheck(_) => None,
        }
    }
}

impl fmt::Display for BilError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BilError::Lex(e) => write!(f, "{}", e),
            BilError::Parse(e) => write!(f, "{}", e),
            BilError::Ontology(errs) => {
                let s: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
                write!(f, "{}", s.join("\n"))
            }
            BilError::Type(errs) => {
                let s: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
                write!(f, "{}", s.join("\n"))
            }
            BilError::Runtime(e) => write!(f, "{}", e),
            BilError::Vm(msg) => write!(f, "{}", msg),
            BilError::Codegen(msg) => write!(f, "{}", msg),
            BilError::ModelCheck(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for BilError {}

impl From<LexError> for BilError {
    fn from(e: LexError) -> Self {
        BilError::Lex(e)
    }
}

impl From<ParseError> for BilError {
    fn from(e: ParseError) -> Self {
        BilError::Parse(e)
    }
}

impl From<Vec<OntologyError>> for BilError {
    fn from(errs: Vec<OntologyError>) -> Self {
        BilError::Ontology(errs)
    }
}

impl From<Vec<TypeError>> for BilError {
    fn from(errs: Vec<TypeError>) -> Self {
        BilError::Type(errs)
    }
}

impl From<RuntimeError> for BilError {
    fn from(e: RuntimeError) -> Self {
        BilError::Runtime(e)
    }
}
