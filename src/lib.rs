#![recursion_limit = "128"]
#![feature(proc_macro)]

extern crate lalr;
//extern crate literalext;
extern crate proc_macro2;
extern crate proc_macro;
#[macro_use]
extern crate quote;
extern crate redfa;
#[macro_use]
extern crate syn;

mod lexer;
mod parser;

use proc_macro::TokenStream;

#[proc_macro]
pub fn lexer(tok: TokenStream) -> TokenStream {
    lexer::lexer(tok)
}

#[proc_macro]
pub fn parser(tok: TokenStream) -> TokenStream {
    parser::parser(tok)
}
