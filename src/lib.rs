#![recursion_limit = "128"]
#![feature(proc_macro_diagnostic)]
#![feature(proc_macro_span)]
#![warn(unused_extern_crates)]

#[cfg(feature = "parser")]
extern crate lalr;
extern crate proc_macro2;
extern crate proc_macro;
#[macro_use]
extern crate quote;
#[cfg(feature = "lexer")]
extern crate redfa;
#[macro_use]
extern crate syn;

#[cfg(feature = "lexer")]
mod lexer;
#[cfg(feature = "parser")]
mod parser;

use proc_macro::TokenStream;

#[cfg(feature = "lexer")]
#[proc_macro]
pub fn lexer(tok: TokenStream) -> TokenStream {
    lexer::lexer(tok.into()).into()
}

#[cfg(feature = "parser")]
#[proc_macro]
pub fn parser(tok: TokenStream) -> TokenStream {
    parser::parser(tok.into()).into()
}
