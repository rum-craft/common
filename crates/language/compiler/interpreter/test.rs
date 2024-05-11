use std::{
  collections::BTreeMap,
  path::{Path, PathBuf},
};

use rum_istring::{CachedString, IString};

use crate::compiler::{
  interpreter::ll::{interpret_ll_function, LLValue},
  parser::{self, parse_LL},
};

use super::{
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
fn run_ll_script() -> RumScriptResult<()> {
  let (input, _) = get_source_file("run_ll_script.lang")?;

  let funct = parse_LL(&input)?;

  dbg!(&funct);

  let mut f32_val: f32 = 0.0;

  let value = interpret_ll_function(&funct, &[
    LLValue::f32(200000.0),
    LLValue::ptr32(&mut f32_val as *mut f32 as *mut _, 1),
  ]);

  if let LLValue::ptr32(ptr, size) = value {
    unsafe {
      dbg!(std::slice::from_raw_parts(ptr as *mut f32, size));
    }
  }

  dbg!((value, f32_val));

  Ok(())
}
