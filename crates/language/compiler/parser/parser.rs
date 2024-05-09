#![allow(unused)]

/// ### `radlr` Rust Parser
///
/// - **GENERATOR**: radlr 1.0.1-beta2
/// - **SOURCE**: UNDEFINED
///
/// #### WARNING WARNING WARNING WARNING
/// #### WARNING WARNING WARNING WARNING
/// #### WARNING WARNING WARNING WARNING
///
/// This is a generated file. Any changes to this file may be **overwritten
/// without notice**.
///
/// #### GNINRAW GNINRAW GNINRAW GNINRAW
/// #### GNINRAW GNINRAW GNINRAW GNINRAW
/// #### GNINRAW GNINRAW GNINRAW GNINRAW
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

use radlr_rust_runtime::{kernel::ByteCodeParserNew, parsers::Parser, types::*, *};
use std::{collections::HashMap, rc::Rc};

const BINARY: &'static [u8] = include_bytes!("./parser.bin");

const NONTERM_NAME_TO_ID: [(&'static str, u32); 1] = [("default",0),];

const TOKEN_ID_TO_STRING: [(u32, &'static str); 35] = [
  (0, r###"Default"###),
  (1, r###"{EOF}"###),
  (10, r###"init"###),
  (11, r###"-"###),
  (12, r###"["###),
  (13, r###"]"###),
  (14, r###"<table_attributes>"###),
  (15, r###"<primary_key_table>"###),
  (16, r###"<sub_table_id>"###),
  (17, r###"("###),
  (18, r###")"###),
  (19, r###","###),
  (2, r###"c:sp"###),
  (
    20, r###"tk:(  ( c:id | "_" ) ( c:id | "_" | c:num )(*) | c:num(+) ( c:id ) ( c:id | "_" | c:num )(*)  )"###
  ),
  (21, r###"test"###),
  (22, r###"."###),
  (23, r###"#"###),
  (24, r###"tk:( c:num(+) )"###),
  (25, r###"for"###),
  (26, r###":init"###),
  (27, r###"<cur_id>"###),
  (28, r###"<table_id>"###),
  (29, r###"tk:( "-"? uint )"###),
  (3, r###"c:nl"###),
  (30, r###"="###),
  (31, r###"<expression>"###),
  (32, r###"<member>"###),
  (33, r###"<sci_num>"###),
  (34, r###"tk:( "-"? c:num(+) ( "." ( c:num(+) )? )? ( ("e" | "E") "-"? c:num(*) )? )"###),
  (4, r###"<comment>"###),
  (5, r###":"###),
  (6, r###"<id>"###),
  (7, r###"tk:( "global" ( " " | "\n" ) )"###),
  (8, r###"{"###),
  (9, r###"}"###),
];

const NONTERM_ID_TO_ADDRESS: [(u32, u32); 1] = [(0, 8),];

const STATE_TO_TOKEN_IDS: [(u32, &'static [u32]); 77] = [
  (1118, &TOKENS_0),
  (1283, &TOKENS_0),
  (1295, &TOKENS_0),
  (1307, &TOKENS_10),
  (1351, &TOKENS_29),
  (1433, &TOKENS_14),
  (1488, &TOKENS_3),
  (1548, &TOKENS_6),
  (1592, &TOKENS_3),
  (1799, &TOKENS_0),
  (190, &TOKENS_3),
  (1901, &TOKENS_28),
  (1951, &TOKENS_19),
  (2006, &TOKENS_13),
  (2055, &TOKENS_3),
  (21, &TOKENS_1),
  (2211, &TOKENS_5),
  (2309, &TOKENS_5),
  (2321, &TOKENS_5),
  (2333, &TOKENS_5),
  (2345, &TOKENS_3),
  (2400, &TOKENS_21),
  (241, &TOKENS_8),
  (2503, &TOKENS_3),
  (2632, &TOKENS_7),
  (2704, &TOKENS_13),
  (2753, &TOKENS_3),
  (2813, &TOKENS_15),
  (2898, &TOKENS_13),
  (2947, &TOKENS_16),
  (299, &TOKENS_3),
  (3014, &TOKENS_13),
  (3063, &TOKENS_3),
  (3123, &TOKENS_16),
  (3190, &TOKENS_13),
  (3239, &TOKENS_2),
  (3251, &TOKENS_22),
  (3325, &TOKENS_3),
  (3454, &TOKENS_17),
  (3516, &TOKENS_3),
  (355, &TOKENS_2),
  (3655, &TOKENS_22),
  (367, &TOKENS_6),
  (3723, &TOKENS_22),
  (3735, &TOKENS_2),
  (3748, &TOKENS_22),
  (3760, &TOKENS_12),
  (3838, &TOKENS_9),
  (3899, &TOKENS_23),
  (4072, &TOKENS_4),
  (411, &TOKENS_20),
  (4123, &TOKENS_11),
  (4195, &TOKENS_4),
  (4365, &TOKENS_18),
  (4427, &TOKENS_3),
  (4488, &TOKENS_9),
  (4549, &TOKENS_18),
  (4561, &TOKENS_18),
  (4573, &TOKENS_9),
  (4634, &TOKENS_23),
  (4807, &TOKENS_4),
  (4859, &TOKENS_2),
  (4871, &TOKENS_6),
  (4915, &TOKENS_24),
  (503, &TOKENS_3),
  (5044, &TOKENS_25),
  (5285, &TOKENS_2),
  (5447, &TOKENS_2),
  (5459, &TOKENS_2),
  (5471, &TOKENS_2),
  (569, &TOKENS_27),
  (613, &TOKENS_26),
  (697, &TOKENS_19),
  (752, &TOKENS_13),
  (801, &TOKENS_3),
  (867, &TOKENS_6),
  (911, &TOKENS_3),
];

const TOKENS_0: [u32;2]=[9,20,];

const TOKENS_1: [u32;4]=[7,10,12,20,];

const TOKENS_10: [u32;1]=[30,];

const TOKENS_11: [u32;3]=[18,19,20,];

const TOKENS_12: [u32;2]=[18,20,];

const TOKENS_13: [u32;1]=[13,];

const TOKENS_14: [u32;2]=[22,30,];

const TOKENS_15: [u32;3]=[5,13,23,];

const TOKENS_16: [u32;2]=[5,13,];

const TOKENS_17: [u32;2]=[11,13,];

const TOKENS_18: [u32;2]=[18,19,];

const TOKENS_19: [u32;1]=[29,];

const TOKENS_2: [u32;5]=[1,7,10,12,20,];

const TOKENS_20: [u32;2]=[25,26,];

const TOKENS_21: [u32;4]=[5,13,22,23,];

const TOKENS_22: [u32;2]=[12,17,];

const TOKENS_23: [u32;2]=[20,24,];

const TOKENS_24: [u32;1]=[21,];

const TOKENS_25: [u32;2]=[9,21,];

const TOKENS_26: [u32;2]=[12,20,];

const TOKENS_27: [u32;1]=[26,];

const TOKENS_28: [u32;1]=[12,];

const TOKENS_29: [u32;1]=[34,];

const TOKENS_3: [u32;1]=[20,];

const TOKENS_4: [u32;1]=[18,];

const TOKENS_5: [u32;3]=[9,25,26,];

const TOKENS_6: [u32;1]=[8,];

const TOKENS_7: [u32;4]=[13,18,19,20,];

const TOKENS_8: [u32;1]=[5,];

const TOKENS_9: [u32;3]=[5,18,19,];


/// Parser database for the "" parser
pub struct ParserDB {
  pub bytecode: &'static [u8],
  pub nonterm_name_to_id: HashMap<&'static str, u32>,
  pub state_to_token_ids_map: HashMap<u32, &'static [u32]>,
  pub nonterm_id_to_address: HashMap<u32, u32>,
  pub token_id_to_str: HashMap<u32, &'static str>,

}

impl ParserDB {
  pub fn new() -> Self {Self {
      bytecode: BINARY,
      nonterm_name_to_id: HashMap::from_iter(NONTERM_NAME_TO_ID),
      state_to_token_ids_map: HashMap::from_iter(STATE_TO_TOKEN_IDS),
      nonterm_id_to_address: HashMap::from_iter(NONTERM_ID_TO_ADDRESS),
      token_id_to_str: HashMap::from_iter(TOKEN_ID_TO_STRING)
    
    }
  
  }

}

impl AsRef<[u8]> for ParserDB {
  fn as_ref(&self) -> &[u8] {
    self.bytecode
  }
}


impl RuntimeDatabase for ParserDB {
  fn default_entrypoint(&self) -> EntryPoint {
      EntryPoint { nonterm_id: 0 }
  }

  fn get_entry_data_from_name(&self, entry_name: &str) -> Result<EntryPoint, ParserError> {
    if let Some(id) = self.nonterm_name_to_id.get(entry_name) {
      Ok(EntryPoint { nonterm_id: *id })
    } else {
      Err(ParserError::InvalidEntryName)
    }
  
  }

  fn get_expected_tok_ids_at_state(&self, state_id: u32) -> Option<&[u32]> {
    self.state_to_token_ids_map.get(&state_id).map(|s| *s)
  }

  fn token_id_to_str(&self, tok_id: u32) -> Option<&str> {
    self.token_id_to_str.get(&tok_id).map(|s| *s)
  }

  fn entrypoints(&self) -> Vec<(std::string::String, u32)> {
    vec![]
  }

}

impl<T: ParserInput> ParserProducer<T> for ParserDB {
  fn get_parser(&self) -> Result<Box<dyn Parser<T>>, ParserError> {
    Ok(Box::new(ByteCodeParserNew::new(Rc::new(self.bytecode), self.nonterm_id_to_address.clone())))
  
  }

}

