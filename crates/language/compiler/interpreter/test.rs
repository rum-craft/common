use crate::compiler::{
  interpreter::ll::{
    interpreter::{BitSize, LLVal, PtrData},
    jit::compile_ll_function,
  },
  parser::{self, parse_ll},
};
use rum_istring::{CachedString, IString};
use std::{
  collections::BTreeMap,
  path::{Path, PathBuf},
};

use super::{
  ll::{jit::optimize_ssa_function, x86::compile_from_ssa_fn},
  runner::{interpret_string, RumScriptResult},
  types::Context,
};

fn get_source_path(file_name: &str) -> Result<PathBuf, std::io::Error> {
  PathBuf::from("/home/work/projects/lib_rum_common/crates/language/test_scripts/")
    .canonicalize()?
    .join(file_name)
    .canonicalize()
}

fn get_source_file(file_name: &str) -> Result<(String, PathBuf), std::io::Error> {
  let path = get_source_path(file_name)?;

  Ok((std::fs::read_to_string(&path)?, path))
}

#[test]
fn write_to_simple_table() -> RumScriptResult<()> {
  let mut ctx = Context::new();

  let (input, _) = get_source_file("write_to_simple_table.lang")?;

  interpret_string(&input, &mut ctx)?;

  Ok(())
}

#[test]
fn compile_ll_script() -> RumScriptResult<()> {
  let (input, _) = get_source_file("run_ll_script.lang")?;

  let funct = parse_ll(&input)?;

  let ssa_fn = compile_ll_function(&funct)?;

  let optimized_ssa_fn = optimize_ssa_function(&ssa_fn);

  compile_from_ssa_fn(&optimized_ssa_fn);

  Ok(())
}
