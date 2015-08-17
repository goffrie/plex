#![feature(plugin_registrar, quote, rustc_private, scoped_tls)]

extern crate lalr;
extern crate regex_dfa;
extern crate syntax;
extern crate rustc;

pub mod lexer;
pub mod parser;

use syntax::ext::base;
use syntax::parse::token;
use rustc::plugin;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut plugin::Registry) {
    reg.register_syntax_extension(token::intern("parser"),
        base::SyntaxExtension::NormalTT(Box::new(parser::expand_parser), None, true));
    reg.register_macro("span", parser::expand_current_span);
    reg.register_syntax_extension(token::intern("lexer"),
        base::SyntaxExtension::NormalTT(Box::new(lexer::expand_lexer), None, true));
}
