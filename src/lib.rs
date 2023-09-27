#![recursion_limit = "128"]
#![warn(unused_extern_crates)]

//! # plex, a parser and lexer generator
//! See README.md for documentation.

#[cfg(feature = "lexer")]
mod lexer;
#[cfg(feature = "parser")]
mod parser;

use proc_macro::TokenStream;

/// Defines a lexer.
#[cfg(feature = "lexer")]
#[proc_macro]
pub fn lexer(tok: TokenStream) -> TokenStream {
    lexer::lexer(tok)
}

/// Defines a parser.
#[cfg(feature = "parser")]
#[proc_macro]
pub fn parser(tok: TokenStream) -> TokenStream {
    parser::parser(tok)
}
