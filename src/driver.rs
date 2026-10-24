//! High-level compilation, verification, model-checking, and execution pipeline driver.

use crate::ast::Program;
use crate::codegen::{self, NativeBuildReport};
use crate::eval::{Interpreter, Value};
use crate::ir::MultiLevelIr;
use crate::lexer;
use crate::model_check::{self, ModelCheckReport};
use crate::ontology::OntologyRegistry;
use crate::parser::Parser;
use crate::smt::{self, Prover, ProverResult, SubsumptionResult};
use crate::types::TypeEnv;
use crate::verus;
use crate::vm::{BytecodeProgram, BytecodeVm};
use crate::wp::{self, ProofObligation};
use std::path::Path;

pub fn lower_ir_source(src: &str) -> Result<MultiLevelIr, String> {
    let (program, ontology, mut tenv) = check_source(src)?;
    Ok(MultiLevelIr::build(&program, &ontology, &mut tenv))
}

pub fn run_vm_source(
    src: &str,
    seed: u64,
) -> Result<(Vec<(String, Value)>, BytecodeProgram), String> {
    let (program, ontology, mut tenv) = check_source(src)?;
    let ir = MultiLevelIr::build(&program, &ontology, &mut tenv);
    let bc = BytecodeProgram::compile(&ir.lir, &ir.hir);
    let mut vm = BytecodeVm::new(ontology, bc.clone(), seed);
    let outputs = vm.execute()?;
    Ok((outputs, bc))
}

pub fn build_native_source(src: &str, output_bin: &Path) -> Result<NativeBuildReport, String> {
    let (program, ontology, mut tenv) = check_source(src)?;
    let ir = MultiLevelIr::build(&program, &ontology, &mut tenv);
    codegen::compile_native_binary(&ir.lir, &ir.hir, output_bin)
}

pub fn emit_verus_source(src: &str) -> Result<String, String> {
    let (program, ontology, _) = check_source(src)?;
    Ok(verus::emit_verus_rust(&program, &ontology))
}

pub fn solve_ontology_source(src: &str, prover: Prover) -> Result<(ProverResult, String), String> {
    let (program, ontology, _) = check_source(src)?;
    let smt2 = smt::emit_ontology_consistency_smt2(&program, &ontology);
    let res = smt::check_ontology_consistency(&program, &ontology, prover);
    Ok((res, smt2))
}

pub fn prove_subsumption_source(
    src: &str,
    child: &str,
    parent: &str,
    prover: Prover,
) -> Result<SubsumptionResult, String> {
    let (program, ontology, _) = check_source(src)?;
    Ok(smt::prove_subsumption(&program, &ontology, child, parent, prover))
}

pub fn parse_source_typed(src: &str) -> Result<Program, crate::error::BilError> {
    let tokens = lexer::tokenize(src)?;
    let mut parser = Parser::new(tokens);
    let mut program = parser.parse_program()?;
    crate::timed::lower_program(&mut program)?;
    Ok(program)
}

pub fn check_source_typed(
    src: &str,
) -> Result<(Program, OntologyRegistry, TypeEnv), crate::error::BilError> {
    let program = parse_source_typed(src)?;
    let ontology = OntologyRegistry::build(&program)?;
    let mut tenv = TypeEnv::new(ontology.clone());
    tenv.check_program(&program)?;
    Ok((program, ontology, tenv))
}

pub type RunOutput = (Vec<(String, Value)>, Vec<String>);

pub fn run_source_typed(
    src: &str,
    seed: u64,
    trace: bool,
) -> Result<RunOutput, crate::error::BilError> {
    let (program, ontology, _) = check_source_typed(src)?;
    let mut interp = Interpreter::new(ontology, seed, trace);
    let outputs = interp.run_program(&program)?;
    Ok((outputs, interp.trace_log))
}

pub fn parse_source(src: &str) -> Result<Program, String> {
    parse_source_typed(src).map_err(|e| e.to_string())
}

pub fn check_source(src: &str) -> Result<(Program, OntologyRegistry, TypeEnv), String> {
    check_source_typed(src).map_err(|e| e.to_string())
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
) -> Result<RunOutput, String> {
    run_source_typed(src, seed, trace).map_err(|e| e.to_string())
}

/// Memoized compilation session (`P3.3`) that parses, validates OntoLogic DAGs,
/// and typechecks once, caching the lowered 3-level IR across verification,
/// model-checking, and execution passes.
pub struct CompilationSession {
    pub program: Program,
    pub ontology: OntologyRegistry,
    pub tenv: TypeEnv,
    ir: Option<MultiLevelIr>,
}

impl CompilationSession {
    pub fn from_source(src: &str) -> Result<Self, String> {
        let (program, ontology, tenv) = check_source(src)?;
        Ok(Self {
            program,
            ontology,
            tenv,
            ir: None,
        })
    }

    pub fn lower_ir(&mut self) -> &MultiLevelIr {
        if self.ir.is_none() {
            let built = MultiLevelIr::build(&self.program, &self.ontology, &mut self.tenv);
            self.ir = Some(built);
        }
        self.ir.as_ref().unwrap()
    }

    pub fn verify(&self) -> Vec<ProofObligation> {
        wp::verify_program(&self.program, &self.ontology)
    }

    pub fn model_check(&self, max_states: usize) -> Result<Vec<ModelCheckReport>, String> {
        model_check::model_check_program(&self.program, &self.ontology, max_states)
    }

    pub fn symbolic_bmc(&self, k: usize, prover: Prover) -> Vec<model_check::SymbolicBmcReport> {
        model_check::symbolic_bmc_program(&self.program, &self.ontology, k, prover)
    }

    pub fn run(&self, seed: u64, trace: bool) -> Result<RunOutput, String> {
        let mut interp = Interpreter::new(self.ontology.clone(), seed, trace);
        let outputs = interp.run_program(&self.program).map_err(|e| e.to_string())?;
        Ok((outputs, interp.trace_log))
    }
}

