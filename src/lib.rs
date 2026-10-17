pub mod ast;
pub mod eval;
pub mod lexer;
pub mod model_check;
pub mod ontology;
pub mod parser;
pub mod types;
pub mod verus;
pub mod wp;

use ast::Program;
use eval::{Interpreter, Value};
use model_check::ModelCheckReport;
use ontology::OntologyRegistry;
use parser::Parser;
use types::TypeEnv;
use wp::ProofObligation;

pub fn emit_verus_source(src: &str) -> Result<String, String> {
    let (program, ontology, _) = check_source(src)?;
    Ok(verus::emit_verus_rust(&program, &ontology))
}

pub fn parse_source(src: &str) -> Result<Program, String> {
    let tokens = lexer::tokenize(src).map_err(|e| e.to_string())?;
    let mut parser = Parser::new(tokens);
    parser.parse_program().map_err(|e| e.to_string())
}

pub fn check_source(src: &str) -> Result<(Program, OntologyRegistry, TypeEnv), String> {
    let program = parse_source(src)?;
    let ontology = OntologyRegistry::build(&program).map_err(|errs| {
        errs.iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    let mut tenv = TypeEnv::new(ontology.clone());
    tenv.check_program(&program).map_err(|errs| {
        errs.iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    Ok((program, ontology, tenv))
}

pub fn verify_source(src: &str) -> Result<Vec<ProofObligation>, String> {
    let (program, ontology, _) = check_source(src)?;
    Ok(wp::verify_program(&program, &ontology))
}

pub fn model_check_source(
    src: &str,
    max_states: usize,
) -> Result<Vec<ModelCheckReport>, String> {
    let (program, ontology, _) = check_source(src)?;
    model_check::model_check_program(&program, &ontology, max_states)
}

pub fn run_source(
    src: &str,
    seed: u64,
    trace: bool,
) -> Result<(Vec<(String, Value)>, Vec<String>), String> {
    let (program, ontology, _) = check_source(src)?;
    let mut interp = Interpreter::new(ontology, seed, trace);
    let outputs = interp.run_program(&program).map_err(|e| e.to_string())?;
    Ok((outputs, interp.trace_log))
}
