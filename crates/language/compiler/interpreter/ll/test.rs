use std::path::PathBuf;

use crate::compiler::{interpreter::error::RumResult, parser::parse_ll};

use super::{ssa_block_compiler::compile_function_blocks, x86::compile_from_ssa_fn};

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
fn construct_function_blocks() -> RumResult<()> {
  let (input, _) = get_source_file("run_ll_script.lang")?;

  let funct = parse_ll(&input)?;

  let blocks = compile_function_blocks(&funct)?;

  compile_from_ssa_fn(&blocks);

  Ok(())
}
