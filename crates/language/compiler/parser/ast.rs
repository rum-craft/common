#![allow(unused)]
#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

/// ### `radlr` Rust Parser
///
/// - **GENERATOR**: radlr 1.0.0-beta2
/// - **SOURCE**: UNDEFINED
///
/// #### WARNING:
///
/// This is a generated file. Any changes to this file may be **overwritten
/// without notice**.
///
/// #### License:
/// Copyright (c) 2020-2024 Anthony Weathersby
///
/// Permission is hereby granted, free of charge, to any person obtaining a copy
/// of this software and associated documentation files (the 'Software'), to
/// deal in the Software without restriction, including without limitation the
/// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
/// sell copies of the Software, and to permit persons to whom the Software is
/// furnished to do so, subject to the following conditions:
///
/// The above copyright notice and this permission notice shall be included in
/// all copies or substantial portions of the Software.
///
/// THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
/// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
/// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
/// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
/// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
/// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
/// IN THE SOFTWARE

use radlr_rust_runtime::parsers::ast::{Tk, Reducer, Node};
use std::collections::HashMap;

#[derive(Clone, Debug, Default)]
#[repr(C,u32)]
pub enum ASTNode<Token:Tk> {
  #[default]
  None, 
  Token(Token), 
  U32(u32), 
  F64(f64), 
  String(String), 
  VecString(Vec<String>), 
  VecRowType(Vec<Box<RowType>>), 
  VecAssignStatement(Vec<Box<AssignStatement>>), 
  VecRowAliasDeclaration(Vec<Box<RowAliasDeclaration>>), 
  /*0*/ 
  VecRoot_blocksValues(/*0*/Vec<Root_blocksValues<Token>>), 
  /*2*/ 
  VecTable_initializationValues(/*2*/Vec<Table_initializationValues<Token>>), 
  VecToken(Vec<Token>), 
  Root_blocksValues(Root_blocksValues<Token>), 
  Table_row_typesValues(Table_row_typesValues), 
  Table_initializationValues(Table_initializationValues<Token>), 
  Member(Box<Member>), 
  TableId(Box<TableId<Token>>), 
  RowType(Box<RowType>), 
  CursorId(Box<CursorId<Token>>), 
  InitExeBlock(Box<InitExeBlock<Token>>), 
  TableIdentifier(Box<TableIdentifier>), 
  TableDefinition(Box<TableDefinition<Token>>), 
  TableZeroInit(Box<TableZeroInit<Token>>), 
  RowTypeDeclaration(Box<RowTypeDeclaration>), 
  TableInit(Box<TableInit<Token>>), 
  NumLiteral(Box<NumLiteral>), 
  AssignStatement(Box<AssignStatement>), 
  GlobalTable(Box<GlobalTable<Token>>), 
  UniformTypeDeclaration(Box<UniformTypeDeclaration>), 
  NamedExeBlock(Box<NamedExeBlock<Token>>), 
  RowAliasDeclaration(Box<RowAliasDeclaration>), 
  RumScript(Box<RumScript<Token>>), 
}

impl<Token:Tk> ASTNode<Token>{pub fn to_token(self) -> Option<Token> {match self {ASTNode::Token(val) => Some(val),_ => None,}}}

impl<Token:Tk> ASTNode<Token>{pub fn into_U32(self) -> Option<u32> {match self {ASTNode::U32(val) => Some(val),_ => None,}}}

impl<Token:Tk> From<u32> for ASTNode<Token>{fn from(value:u32) -> Self {Self::U32(value)}}

impl<Token:Tk> ASTNode<Token>{pub fn into_F64(self) -> Option<f64> {match self {ASTNode::F64(val) => Some(val),_ => None,}}}

impl<Token:Tk> From<f64> for ASTNode<Token>{fn from(value:f64) -> Self {Self::F64(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_String(self) -> Option<String> {match self {ASTNode::String(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<String> for ASTNode<Token>{fn from(value:String) -> Self {Self::String(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_VecString(self) -> Option<Vec<String>> {match self {ASTNode::VecString(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Vec<String>> for ASTNode<Token>{fn from(value:Vec<String>) -> Self {Self::VecString(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_VecRowType(self) -> Option<Vec<Box<RowType>>> {match self {ASTNode::VecRowType(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Vec<Box<RowType>>> for ASTNode<Token>{fn from(value:Vec<Box<RowType>>) -> Self {Self::VecRowType(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_VecAssignStatement(self) -> Option<Vec<Box<AssignStatement>>> {match self {ASTNode::VecAssignStatement(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Vec<Box<AssignStatement>>> for ASTNode<Token>{fn from(value:Vec<Box<AssignStatement>>) -> Self {Self::VecAssignStatement(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_VecRowAliasDeclaration(self) -> Option<Vec<Box<RowAliasDeclaration>>> {match self {ASTNode::VecRowAliasDeclaration(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Vec<Box<RowAliasDeclaration>>> for ASTNode<Token>{fn from(value:Vec<Box<RowAliasDeclaration>>) -> Self {Self::VecRowAliasDeclaration(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_VecRoot_blocksValues(self) -> Option</*0*/Vec<Root_blocksValues<Token>>> {match self {ASTNode::VecRoot_blocksValues(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From</*0*/Vec<Root_blocksValues<Token>>> for ASTNode<Token>{fn from(value:/*0*/Vec<Root_blocksValues<Token>>) -> Self {Self::VecRoot_blocksValues(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_VecTable_initializationValues(self) -> Option</*2*/Vec<Table_initializationValues<Token>>> {match self {ASTNode::VecTable_initializationValues(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From</*2*/Vec<Table_initializationValues<Token>>> for ASTNode<Token>{
  fn from(value:/*2*/Vec<Table_initializationValues<Token>>) -> Self {Self::VecTable_initializationValues(value)}
}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_VecToken(self) -> Option<Vec<Token>> {match self {ASTNode::VecToken(val) => Some(val),_ => None,}}
}

#[derive(Clone, Debug, Default)]
pub enum Root_blocksValues<Token:Tk>{
  #[default]
  None,
  InitExeBlock(Box<InitExeBlock<Token>>), 
  TableDefinition(Box<TableDefinition<Token>>), 
  GlobalTable(Box<GlobalTable<Token>>), 
  NamedExeBlock(Box<NamedExeBlock<Token>>), 
}

#[derive(Clone, Debug, Default)]
pub enum Table_row_typesValues{
  #[default]
  None,
  RowTypeDeclaration(Box<RowTypeDeclaration>), 
  UniformTypeDeclaration(Box<UniformTypeDeclaration>), 
}

#[derive(Clone, Debug, Default)]
pub enum Table_initializationValues<Token:Tk>{#[default]None,TableZeroInit(Box<TableZeroInit<Token>>), TableInit(Box<TableInit<Token>>), }

impl<Token:Tk> ASTNode<Token>{
  pub fn into_Root_blocksValues(self) -> Option<Root_blocksValues<Token>> {
    match self {
      ASTNode::Root_blocksValues(val) => Some(val),
      ASTNode::InitExeBlock(val) => Some(Root_blocksValues::InitExeBlock(val)),
      ASTNode::TableDefinition(val) => Some(Root_blocksValues::TableDefinition(val)),
      ASTNode::GlobalTable(val) => Some(Root_blocksValues::GlobalTable(val)),
      ASTNode::NamedExeBlock(val) => Some(Root_blocksValues::NamedExeBlock(val)),
      _ => None,
    }
  }
}

impl<Token:Tk> From<Root_blocksValues<Token>> for ASTNode<Token>{fn from(value: Root_blocksValues<Token>) -> Self {Self::Root_blocksValues(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_Table_row_typesValues(self) -> Option<Table_row_typesValues> {
    match self {
      ASTNode::Table_row_typesValues(val) => Some(val),
      ASTNode::RowTypeDeclaration(val) => Some(Table_row_typesValues::RowTypeDeclaration(val)),
      ASTNode::UniformTypeDeclaration(val) => Some(Table_row_typesValues::UniformTypeDeclaration(val)),
      _ => None,
    }
  }
}

impl<Token:Tk> From<Table_row_typesValues> for ASTNode<Token>{fn from(value: Table_row_typesValues) -> Self {Self::Table_row_typesValues(value)}}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_Table_initializationValues(self) -> Option<Table_initializationValues<Token>> {
    match self {
      ASTNode::Table_initializationValues(val) => Some(val),
      ASTNode::TableZeroInit(val) => Some(Table_initializationValues::TableZeroInit(val)),
      ASTNode::TableInit(val) => Some(Table_initializationValues::TableInit(val)),
      _ => None,
    }
  }
}

impl<Token:Tk> From<Table_initializationValues<Token>> for ASTNode<Token>{fn from(value: Table_initializationValues<Token>) -> Self {Self::Table_initializationValues(value)}}

impl<Token:Tk> ASTNode<Token> {
  pub fn token (&self) -> Token {
    match self {
      ASTNode::TableId(n) => {n.tok.clone()}
      ASTNode::CursorId(n) => {n.tok.clone()}
      ASTNode::TableDefinition(n) => {n.tok.clone()}
      ASTNode::GlobalTable(n) => {n.tok.clone()}
      ASTNode::Token(tok) => tok.clone(),_ => Default::default()
    }
  }
}

/*impl<Token:Tk> std::hash::Hash for ASTNode<Token> {
  fn hash<H: std::hash::Hasher>(&self, hasher: &mut H){match self{
      ASTNode::Member(n) => n.hash(hasher),
      ASTNode::TableId(n) => n.hash(hasher),
      ASTNode::RowType(n) => n.hash(hasher),
      ASTNode::CursorId(n) => n.hash(hasher),
      ASTNode::InitExeBlock(n) => n.hash(hasher),
      ASTNode::TableIdentifier(n) => n.hash(hasher),
      ASTNode::TableDefinition(n) => n.hash(hasher),
      ASTNode::TableZeroInit(n) => n.hash(hasher),
      ASTNode::RowTypeDeclaration(n) => n.hash(hasher),
      ASTNode::TableInit(n) => n.hash(hasher),
      ASTNode::NumLiteral(n) => n.hash(hasher),
      ASTNode::AssignStatement(n) => n.hash(hasher),
      ASTNode::GlobalTable(n) => n.hash(hasher),
      ASTNode::UniformTypeDeclaration(n) => n.hash(hasher),
      ASTNode::NamedExeBlock(n) => n.hash(hasher),
      ASTNode::RowAliasDeclaration(n) => n.hash(hasher),
      ASTNode::RumScript(n) => n.hash(hasher),
      _=>{}
    }
  }
}*/

#[derive( Clone, Debug, Default )]
pub struct Member{pub scopes: Vec<String>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_Member(self) -> Option<Box<Member>> {match self {ASTNode::Member(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<Member>> for ASTNode<Token>{fn from(value: Box<Member>) -> Self {Self::Member(value)}}

#[derive( Clone, Debug, Default )]
pub struct TableId<Token:Tk>{pub id: String,pub tok: Token,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_TableId(self) -> Option<Box<TableId<Token>>> {match self {ASTNode::TableId(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<TableId<Token>>> for ASTNode<Token>{fn from(value: Box<TableId<Token>>) -> Self {Self::TableId(value)}}

#[derive( Clone, Debug, Default )]
pub struct RowType{pub name: String,pub attributes: Vec<String>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_RowType(self) -> Option<Box<RowType>> {match self {ASTNode::RowType(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<RowType>> for ASTNode<Token>{fn from(value: Box<RowType>) -> Self {Self::RowType(value)}}

#[derive( Clone, Debug, Default )]
pub struct CursorId<Token:Tk>{pub id: String,pub tok: Token,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_CursorId(self) -> Option<Box<CursorId<Token>>> {match self {ASTNode::CursorId(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<CursorId<Token>>> for ASTNode<Token>{fn from(value: Box<CursorId<Token>>) -> Self {Self::CursorId(value)}}

#[derive( Clone, Debug, Default )]
pub struct InitExeBlock<Token:Tk>{pub stmts: /*2*/Vec<Table_initializationValues<Token>>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_InitExeBlock(self) -> Option<Box<InitExeBlock<Token>>> {match self {ASTNode::InitExeBlock(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<InitExeBlock<Token>>> for ASTNode<Token>{fn from(value: Box<InitExeBlock<Token>>) -> Self {Self::InitExeBlock(value)}}

#[derive( Clone, Debug, Default )]
pub struct TableIdentifier{pub id: String,pub sub_id: String,pub attributes: Vec<String>,pub primary_key: String,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_TableIdentifier(self) -> Option<Box<TableIdentifier>> {match self {ASTNode::TableIdentifier(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<TableIdentifier>> for ASTNode<Token>{fn from(value: Box<TableIdentifier>) -> Self {Self::TableIdentifier(value)}}

#[derive( Clone, Debug, Default )]
pub struct TableDefinition<Token:Tk>{
  pub id: Box<TableIdentifier>,
  pub tok: Token,
  pub types: Table_row_typesValues,
  pub aliases: Vec<Box<RowAliasDeclaration>>,
}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_TableDefinition(self) -> Option<Box<TableDefinition<Token>>> {match self {ASTNode::TableDefinition(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<TableDefinition<Token>>> for ASTNode<Token>{fn from(value: Box<TableDefinition<Token>>) -> Self {Self::TableDefinition(value)}}

#[derive( Clone, Debug, Default )]
pub struct TableZeroInit<Token:Tk>{pub rows: u32,pub table_name: Box<TableId<Token>>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_TableZeroInit(self) -> Option<Box<TableZeroInit<Token>>> {match self {ASTNode::TableZeroInit(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<TableZeroInit<Token>>> for ASTNode<Token>{fn from(value: Box<TableZeroInit<Token>>) -> Self {Self::TableZeroInit(value)}}

#[derive( Clone, Debug, Default )]
pub struct RowTypeDeclaration{pub types: Vec<Box<RowType>>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_RowTypeDeclaration(self) -> Option<Box<RowTypeDeclaration>> {match self {ASTNode::RowTypeDeclaration(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<RowTypeDeclaration>> for ASTNode<Token>{fn from(value: Box<RowTypeDeclaration>) -> Self {Self::RowTypeDeclaration(value)}}

#[derive( Clone, Debug, Default )]
pub struct TableInit<Token:Tk>{
  pub rows: u32,
  pub stmts: Vec<Box<AssignStatement>>,
  pub table_name: Box<TableId<Token>>,
  pub cursor_name: Box<CursorId<Token>>,
}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_TableInit(self) -> Option<Box<TableInit<Token>>> {match self {ASTNode::TableInit(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<TableInit<Token>>> for ASTNode<Token>{fn from(value: Box<TableInit<Token>>) -> Self {Self::TableInit(value)}}

#[derive( Clone, Debug, Default )]
pub struct NumLiteral{pub num: f64,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_NumLiteral(self) -> Option<Box<NumLiteral>> {match self {ASTNode::NumLiteral(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<NumLiteral>> for ASTNode<Token>{fn from(value: Box<NumLiteral>) -> Self {Self::NumLiteral(value)}}

#[derive( Clone, Debug, Default )]
pub struct AssignStatement{pub left: Box<Member>,pub right: Box<NumLiteral>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_AssignStatement(self) -> Option<Box<AssignStatement>> {match self {ASTNode::AssignStatement(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<AssignStatement>> for ASTNode<Token>{fn from(value: Box<AssignStatement>) -> Self {Self::AssignStatement(value)}}

#[derive( Clone, Debug, Default )]
pub struct GlobalTable<Token:Tk>{pub tok: Token,pub name: String,pub table_def_name: String,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_GlobalTable(self) -> Option<Box<GlobalTable<Token>>> {match self {ASTNode::GlobalTable(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<GlobalTable<Token>>> for ASTNode<Token>{fn from(value: Box<GlobalTable<Token>>) -> Self {Self::GlobalTable(value)}}

#[derive( Clone, Debug, Default )]
pub struct UniformTypeDeclaration{pub r#type: String,pub size: u32,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_UniformTypeDeclaration(self) -> Option<Box<UniformTypeDeclaration>> {match self {ASTNode::UniformTypeDeclaration(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<UniformTypeDeclaration>> for ASTNode<Token>{fn from(value: Box<UniformTypeDeclaration>) -> Self {Self::UniformTypeDeclaration(value)}}

#[derive( Clone, Debug, Default )]
pub struct NamedExeBlock<Token:Tk>{pub name: String,pub stmts: Vec<Token>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_NamedExeBlock(self) -> Option<Box<NamedExeBlock<Token>>> {match self {ASTNode::NamedExeBlock(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<NamedExeBlock<Token>>> for ASTNode<Token>{fn from(value: Box<NamedExeBlock<Token>>) -> Self {Self::NamedExeBlock(value)}}

#[derive( Clone, Debug, Default )]
pub struct RowAliasDeclaration{pub names: Vec<String>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_RowAliasDeclaration(self) -> Option<Box<RowAliasDeclaration>> {match self {ASTNode::RowAliasDeclaration(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<RowAliasDeclaration>> for ASTNode<Token>{fn from(value: Box<RowAliasDeclaration>) -> Self {Self::RowAliasDeclaration(value)}}

#[derive( Clone, Debug, Default )]
pub struct RumScript<Token:Tk>{pub statements: /*3*/Vec<Root_blocksValues<Token>>,}

impl<Token:Tk> ASTNode<Token>{
  pub fn into_RumScript(self) -> Option<Box<RumScript<Token>>> {match self {ASTNode::RumScript(val) => Some(val),_ => None,}}
}

impl<Token:Tk> From<Box<RumScript<Token>>> for ASTNode<Token>{fn from(value: Box<RumScript<Token>>) -> Self {Self::RumScript(value)}}
  

fn rule_0/*{ t_RumScript, statements: $1 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let statements = std::mem::take(&mut nodes[0]);
  let statements = unsafe{ statements.into_VecRoot_blocksValues().unwrap_unchecked() };
  
  ASTNode::RumScript(Box::new(RumScript{statements,}))
}

fn rule_1/*statement*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_Root_blocksValues().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_2/*statement(+)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[1]);
  let out_r = unsafe{ out_r.into_Root_blocksValues().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecRoot_blocksValues().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_3/*table::definition*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[0]);
  let out = unsafe{ out.into_TableDefinition().unwrap_unchecked() };
  out.into()
}

fn rule_4/*global_table*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[0]);
  let out = unsafe{ out.into_GlobalTable().unwrap_unchecked() };
  out.into()
}

fn rule_5/*exe::root_blocks*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[0]);
  let out = unsafe{ out.into_Root_blocksValues().unwrap_unchecked() };
  out.into()
}

fn rule_6/*{ t_TableDefinition, id:$1, aliases:$2, types:$3, tok }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[0]);
  let id = unsafe{ id.into_TableIdentifier().unwrap_unchecked() };
  
  let tok = nterm_tok.clone();
  
  let types = std::mem::take(&mut nodes[2]);
  let types = unsafe{ types.into_Table_row_typesValues().unwrap_unchecked() };
  
  let aliases = std::mem::take(&mut nodes[1]);
  let aliases = unsafe{ aliases.into_VecRowAliasDeclaration().unwrap_unchecked() };
  
  ASTNode::TableDefinition(Box::new(TableDefinition{id,tok,types,aliases,}))
}

fn rule_7/*{ t_TableDefinition, id:$1, aliases:$2, types:$3, tok }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[0]);
  let id = unsafe{ id.into_TableIdentifier().unwrap_unchecked() };
  
  let tok = nterm_tok.clone();
  
  let types = std::mem::take(&mut nodes[1]);
  let types = unsafe{ types.into_Table_row_typesValues().unwrap_unchecked() };
  
  let aliases = Default::default();
  
  ASTNode::TableDefinition(Box::new(TableDefinition{id,tok,types,aliases,}))
}

fn rule_8/*table_row_aliases*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_RowAliasDeclaration().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_9/*table_row_aliases(*)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[1]);
  let out_r = unsafe{ out_r.into_RowAliasDeclaration().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecRowAliasDeclaration().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_10/*{ t_GlobalTable, name, table_def_name: $table_def, tok }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let tok = nterm_tok.clone();
  
  let name = std::mem::take(&mut nodes[1]);
  let name = unsafe{ name.into_String().unwrap_unchecked() };
  
  let table_def_name = std::mem::take(&mut nodes[3]);
  let table_def_name = unsafe{ table_def_name.into_String().unwrap_unchecked() };
  
  ASTNode::GlobalTable(Box::new(GlobalTable{tok,name,table_def_name,}))
}

fn rule_11/*{ t_InitExeBlock, name, stmts }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let stmts = std::mem::take(&mut nodes[2]);
  let stmts = unsafe{ stmts.into_VecTable_initializationValues().unwrap_unchecked() };
  
  ASTNode::InitExeBlock(Box::new(InitExeBlock{stmts,}))
}

fn rule_12/*{ t_NamedExeBlock, name, stmts }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let name = std::mem::take(&mut nodes[0]);
  let name = unsafe{ name.into_String().unwrap_unchecked() };
  
  let stmts = std::mem::take(&mut nodes[2]);
  let stmts = unsafe{ stmts.into_VecToken().unwrap_unchecked() };
  
  ASTNode::NamedExeBlock(Box::new(NamedExeBlock{name,stmts,}))
}

fn rule_13/*init_block_statements*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_Table_initializationValues().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_14/*init_block_statements(+)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[1]);
  let out_r = unsafe{ out_r.into_Table_initializationValues().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecTable_initializationValues().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_15/*block_statements*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = nodes[0].clone();
  let out_0 = out_0.to_token().unwrap();
  
  let out = vec![ out_0 ];
  ASTNode::VecToken(out)
}

fn rule_16/*block_statements(+)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = nodes[1].clone();
  let out_r = out_r.to_token().unwrap();
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecToken().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  ASTNode::VecToken(out)
}

fn rule_17/*{ t_RowAliasDeclaration, names: $2 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let names = std::mem::take(&mut nodes[1]);
  let names = unsafe{ names.into_VecString().unwrap_unchecked() };
  
  ASTNode::RowAliasDeclaration(Box::new(RowAliasDeclaration{names,}))
}

fn rule_18/*prim::id*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_String().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_19/*prim::id(+"-")*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[2]);
  let out_r = unsafe{ out_r.into_String().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecString().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_20/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = std::mem::take(&mut nodes[2]);
  let sub_id = unsafe{ sub_id.into_String().unwrap_unchecked() };
  
  let attributes = std::mem::take(&mut nodes[4]);
  let attributes = unsafe{ attributes.into_VecString().unwrap_unchecked() };
  
  let primary_key = std::mem::take(&mut nodes[3]);
  let primary_key = unsafe{ primary_key.into_String().unwrap_unchecked() };
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_21/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = Default::default();
  
  let attributes = std::mem::take(&mut nodes[3]);
  let attributes = unsafe{ attributes.into_VecString().unwrap_unchecked() };
  
  let primary_key = std::mem::take(&mut nodes[2]);
  let primary_key = unsafe{ primary_key.into_String().unwrap_unchecked() };
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_22/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = std::mem::take(&mut nodes[2]);
  let sub_id = unsafe{ sub_id.into_String().unwrap_unchecked() };
  
  let attributes = std::mem::take(&mut nodes[3]);
  let attributes = unsafe{ attributes.into_VecString().unwrap_unchecked() };
  
  let primary_key = Default::default();
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_23/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = Default::default();
  
  let attributes = std::mem::take(&mut nodes[2]);
  let attributes = unsafe{ attributes.into_VecString().unwrap_unchecked() };
  
  let primary_key = Default::default();
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_24/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = std::mem::take(&mut nodes[2]);
  let sub_id = unsafe{ sub_id.into_String().unwrap_unchecked() };
  
  let attributes = Default::default();
  
  let primary_key = std::mem::take(&mut nodes[3]);
  let primary_key = unsafe{ primary_key.into_String().unwrap_unchecked() };
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_25/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = Default::default();
  
  let attributes = Default::default();
  
  let primary_key = std::mem::take(&mut nodes[2]);
  let primary_key = unsafe{ primary_key.into_String().unwrap_unchecked() };
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_26/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = std::mem::take(&mut nodes[2]);
  let sub_id = unsafe{ sub_id.into_String().unwrap_unchecked() };
  
  let attributes = Default::default();
  
  let primary_key = Default::default();
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_27/*{ t_TableIdentifier, id: $2, sub_id: $3, primary_key: $4, attributes: $5 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[1]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let sub_id = Default::default();
  
  let attributes = Default::default();
  
  let primary_key = Default::default();
  
  ASTNode::TableIdentifier(Box::new(TableIdentifier{id,sub_id,attributes,primary_key,}))
}

fn rule_28/*{ t_RowTypeDeclaration, types: $2 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let types = std::mem::take(&mut nodes[1]);
  let types = unsafe{ types.into_VecRowType().unwrap_unchecked() };
  
  ASTNode::RowTypeDeclaration(Box::new(RowTypeDeclaration{types,}))
}

fn rule_29/*{ t_RowTypeDeclaration, types: $2 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let types = Default::default();
  
  ASTNode::RowTypeDeclaration(Box::new(RowTypeDeclaration{types,}))
}

fn rule_30/*{ t_UniformTypeDeclaration, type: $2, size: u32($4) }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let r#type = std::mem::take(&mut nodes[1]);
  let r#type = unsafe{ r#type.into_String().unwrap_unchecked() };
  
  let size = nodes[3].clone();
  let size = size.to_token().unwrap();
  let size: u32 = size.to_string().parse().unwrap_or_default();
  
  ASTNode::UniformTypeDeclaration(Box::new(UniformTypeDeclaration{r#type,size,}))
}

fn rule_31/*{ t_RowType, name:$1, attributes:$2 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let name = std::mem::take(&mut nodes[0]);
  let name = unsafe{ name.into_String().unwrap_unchecked() };
  
  let attributes = std::mem::take(&mut nodes[1]);
  let attributes = unsafe{ attributes.into_VecString().unwrap_unchecked() };
  
  ASTNode::RowType(Box::new(RowType{name,attributes,}))
}

fn rule_32/*{ t_RowType, name:$1, attributes:$2 }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let name = std::mem::take(&mut nodes[0]);
  let name = unsafe{ name.into_String().unwrap_unchecked() };
  
  let attributes = Default::default();
  
  ASTNode::RowType(Box::new(RowType{name,attributes,}))
}

fn rule_33/*(prim::id table_attributes? :ast { t_RowType, name:$1, attributes:$2 } )*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_RowType().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_34/*(prim::id table_attributes? :ast { t_RowType, name:$1, attributes:$2 } )(*",")*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[2]);
  let out_r = unsafe{ out_r.into_RowType().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecRowType().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_35/*tk:(  ( c:id | "_" ) ( c:id | "_" | c:num )(*) | c:num(+) ( c:id ) ( c:id | "_" | c:num )(*)  )

    :ast str($1)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {let nodes=unsafe{&mut*nodes};let out = tokens[0].clone();let out = out.to_string();out.into()}

fn rule_36/*table_initialization*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[0]);
  let out = unsafe{ out.into_Table_initializationValues().unwrap_unchecked() };
  out.into()
}

fn rule_37/*"test"*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {let nodes=unsafe{&mut*nodes};let out = tokens[0].clone();ASTNode::Token(out)}

fn rule_38/*"." prim::id*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[1]);
  let out = unsafe{ out.into_String().unwrap_unchecked() };
  out.into()
}

fn rule_39/*"#" prim::id*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[1]);
  let out = unsafe{ out.into_String().unwrap_unchecked() };
  out.into()
}

fn rule_40/*":" prim::id(+)

    :ast $2*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[1]);
  let out = unsafe{ out.into_VecString().unwrap_unchecked() };
  out.into()
}

fn rule_41/*prim::id*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_String().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_42/*prim::id(+)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[1]);
  let out_r = unsafe{ out_r.into_String().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecString().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_43/*tk:( c:num(+) )*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {let nodes=unsafe{&mut*nodes};let out = tokens[0].clone();ASTNode::Token(out)}

fn rule_44/*{ t_TableZeroInit, table_name, rows }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let rows = std::mem::take(&mut nodes[1]);
  let rows = unsafe{ rows.into_U32().unwrap_unchecked() };
  
  let table_name = std::mem::take(&mut nodes[2]);
  let table_name = unsafe{ table_name.into_TableId().unwrap_unchecked() };
  
  ASTNode::TableZeroInit(Box::new(TableZeroInit{rows,table_name,}))
}

fn rule_45/*{ t_TableInit, table_name, cursor_name, rows, stmts }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let rows = std::mem::take(&mut nodes[3]);
  let rows = unsafe{ rows.into_U32().unwrap_unchecked() };
  
  let stmts = std::mem::take(&mut nodes[6]);
  let stmts = unsafe{ stmts.into_VecAssignStatement().unwrap_unchecked() };
  
  let table_name = std::mem::take(&mut nodes[4]);
  let table_name = unsafe{ table_name.into_TableId().unwrap_unchecked() };
  
  let cursor_name = std::mem::take(&mut nodes[1]);
  let cursor_name = unsafe{ cursor_name.into_CursorId().unwrap_unchecked() };
  
  ASTNode::TableInit(Box::new(TableInit{rows,stmts,table_name,cursor_name,}))
}

fn rule_46/*{ t_TableInit, table_name, cursor_name, rows, stmts }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let rows = Default::default();
  
  let stmts = std::mem::take(&mut nodes[5]);
  let stmts = unsafe{ stmts.into_VecAssignStatement().unwrap_unchecked() };
  
  let table_name = std::mem::take(&mut nodes[3]);
  let table_name = unsafe{ table_name.into_TableId().unwrap_unchecked() };
  
  let cursor_name = std::mem::take(&mut nodes[1]);
  let cursor_name = unsafe{ cursor_name.into_CursorId().unwrap_unchecked() };
  
  ASTNode::TableInit(Box::new(TableInit{rows,stmts,table_name,cursor_name,}))
}

fn rule_47/*"[" prim::int "]" :ast u32($2)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = nodes[1].clone();
  let out = out.to_token().unwrap();
  let out: u32 = out.to_string().parse().unwrap_or_default();
  out.into()
}

fn rule_48/*"[" prim::int "]" :ast u32($2)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = nodes[1].clone();
  let out = out.to_token().unwrap();
  let out: u32 = out.to_string().parse().unwrap_or_default();
  out.into()
}

fn rule_49/*init_statements*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_AssignStatement().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_50/*init_statements(+)*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[1]);
  let out_r = unsafe{ out_r.into_AssignStatement().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecAssignStatement().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_51/*tk:( "-"? uint )*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {let nodes=unsafe{&mut*nodes};let out = tokens[0].clone();ASTNode::Token(out)}

fn rule_52/*assignment_statement*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[0]);
  let out = unsafe{ out.into_AssignStatement().unwrap_unchecked() };
  out.into()
}

fn rule_53/*{t_TableId, id:$1, tok}*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[0]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let tok = nterm_tok.clone();
  
  ASTNode::TableId(Box::new(TableId{id,tok,}))
}

fn rule_54/*{t_CursorId, id:$1, tok}*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let id = std::mem::take(&mut nodes[0]);
  let id = unsafe{ id.into_String().unwrap_unchecked() };
  
  let tok = nterm_tok.clone();
  
  ASTNode::CursorId(Box::new(CursorId{id,tok,}))
}

fn rule_55/*{ t_AssignStatement, left, right }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let left = std::mem::take(&mut nodes[0]);
  let left = unsafe{ left.into_Member().unwrap_unchecked() };
  
  let right = std::mem::take(&mut nodes[2]);
  let right = unsafe{ right.into_NumLiteral().unwrap_unchecked() };
  
  ASTNode::AssignStatement(Box::new(AssignStatement{left,right,}))
}

fn rule_56/*{ t_Member, scopes }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let scopes = std::mem::take(&mut nodes[0]);
  let scopes = unsafe{ scopes.into_VecString().unwrap_unchecked() };
  
  ASTNode::Member(Box::new(Member{scopes,}))
}

fn rule_57/*prim::id*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  /*1*/let out_0 = std::mem::take(&mut nodes[0]);
  let out_0 = unsafe{ out_0.into_String().unwrap_unchecked() };
  
  let out = vec![ out_0 ];
  out.into()
}

fn rule_58/*prim::id(+".")*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out_r = std::mem::take(&mut nodes[2]);
  let out_r = unsafe{ out_r.into_String().unwrap_unchecked() };
  let out_l = std::mem::take(&mut nodes[0]);
  let out_l = unsafe{ out_l.into_VecString().unwrap_unchecked() };
  let mut out = out_l;
  out.push(out_r);
  out.into()
}

fn rule_59/*num*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  let out = std::mem::take(&mut nodes[0]);
  let out = unsafe{ out.into_NumLiteral().unwrap_unchecked() };
  out.into()
}

fn rule_60/*{ t_NumLiteral, num: f64($num) }*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {
  let nodes=unsafe{&mut*nodes};
  
  let num = nodes[0].clone();
  let num = num.to_token().unwrap();
  let num: f64 = num.to_string().parse().unwrap_or_default();
  
  ASTNode::NumLiteral(Box::new(NumLiteral{num,}))
}

fn rule_61/*tk:( "-"? c:num(+) ( "." ( c:num(+) )? )? ( ("e" | "E") "-"? c:num(*) )? )*/<Token:Tk>( nodes: *mut [ASTNode<Token>], tokens:&[Token], nterm_tok: Token) -> ASTNode<Token> {let nodes=unsafe{&mut*nodes};let out = tokens[0].clone();ASTNode::Token(out)}

pub struct ReduceRules<Token:Tk>(pub [Reducer<Token,ASTNode<Token>>;62]);

impl<Token:Tk> ReduceRules<Token>{
  pub const fn new() -> Self {
    Self([
        rule_0, 
        rule_1, 
        rule_2, 
        rule_3, 
        rule_4, 
        rule_5, 
        rule_6, 
        rule_7, 
        rule_8, 
        rule_9, 
        rule_10, 
        rule_11, 
        rule_12, 
        rule_13, 
        rule_14, 
        rule_15, 
        rule_16, 
        rule_17, 
        rule_18, 
        rule_19, 
        rule_20, 
        rule_21, 
        rule_22, 
        rule_23, 
        rule_24, 
        rule_25, 
        rule_26, 
        rule_27, 
        rule_28, 
        rule_29, 
        rule_30, 
        rule_31, 
        rule_32, 
        rule_33, 
        rule_34, 
        rule_35, 
        rule_36, 
        rule_37, 
        rule_38, 
        rule_39, 
        rule_40, 
        rule_41, 
        rule_42, 
        rule_43, 
        rule_44, 
        rule_45, 
        rule_46, 
        rule_47, 
        rule_48, 
        rule_49, 
        rule_50, 
        rule_51, 
        rule_52, 
        rule_53, 
        rule_54, 
        rule_55, 
        rule_56, 
        rule_57, 
        rule_58, 
        rule_59, 
        rule_60, 
        rule_61, 
      ]
    )
  }
}

impl<Token:Tk> AsRef<[Reducer<Token, ASTNode<Token>>]> for ReduceRules<Token>{fn as_ref(&self) -> &[Reducer<Token, ASTNode<Token>>]{&self.0}}