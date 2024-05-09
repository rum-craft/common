use radlr_rust_runtime::{
  parsers::ast::{AstDatabase, Tk},
  types::{ParserProducer, RuntimeDatabase, StringInput},
};

mod ast;
mod parser;

pub use radlr_rust_runtime::types::Token;

pub use ast::*;

pub type ASTNode = ast::ASTNode<radlr_rust_runtime::types::Token>;

pub fn parse(input: &str) -> Result<ASTNode, String> {
  let parser_db = parser::ParserDB::new();
  match parser_db.build_ast(
    &mut StringInput::from(input),
    parser_db.default_entrypoint(),
    ast::ReduceRules::<radlr_rust_runtime::types::Token>::new(),
  ) {
    Err(err) => {
      println!("{err:?}");
      Err("Failed to parse input".to_string())
    }
    Ok(node) => Ok(node),
  }
}
