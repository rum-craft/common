#![feature(proc_macro_span)]

extern crate proc_macro;
use proc_macro::{Span, TokenStream, TokenTree};

fn process_arg(stream: TokenStream) -> (String, String, usize, usize) {
  let mut name = "undefined".to_ascii_lowercase();
  let mut src = String::new();
  let mut line = 0;
  let mut col = 0;

  let mut iter = stream.into_iter().peekable();

  if iter.peek().is_none() {
    panic!("Should pass a str argument as the block identifier \n e.g: rum_profile::profile_block!(\"identifier\");");
  }

  for arg in iter {
    match &arg {
      TokenTree::Literal(literal) => {
        let span = &literal.span();
        name = literal.to_string();
        src = span.source_file().path().to_str().unwrap().to_string();
        line = span.line();
        col = Span::call_site().column();
      }
      _ => {}
    }
  }
  (name, src, line, col)
}

fn create_profile_init_block(name: String, src: String, line: usize, col: usize) -> String {
  format!("
  unsafe {{
    use std::hint::black_box;
    use std::sync::atomic::Ordering::Relaxed;
    pub static LOCAL_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(u64::MAX);

    let local_id = LOCAL_ID.load(Relaxed);

    let id = if(local_id == u64::MAX) {{
      let _ = LOCAL_ID.compare_exchange_weak(local_id, rum_profile::GLOBAL_ID_COUNTER.fetch_add(1, Relaxed), Relaxed, Relaxed);
      LOCAL_ID.load(Relaxed)
    }} else {{
      local_id
    }};

    black_box(rum_profile::ProfileBlock::new(id, \"{}\", \"{}:{}:{}\", {line}))
  }}", name.replace("\"", ""), src, line ,col)
}

#[proc_macro]
pub fn profile_block(stream: TokenStream) -> TokenStream {
  let (name, src, line, col) = process_arg(stream);

  let val = create_profile_init_block(name, src, line, col);

  ("#[allow(unused, non_snake_case)]
  let __PROFILE_ENTRY__ ="
    .to_string()
    + &val
    + ";")
    .parse()
    .unwrap()
}

#[proc_macro]
pub fn profile_block_droppable(stream: TokenStream) -> TokenStream {
  let (name, src, line, col) = process_arg(stream);

  let val = create_profile_init_block(name, src, line, col);

  (val + ";").parse().unwrap()
}
