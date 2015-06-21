#![feature(plugin_registrar, quote, rustc_private, collections, scoped_tls)]

extern crate lalr;
extern crate regex_dfa;
extern crate syntax;
extern crate rustc;

pub mod lexer;
pub mod parser;
