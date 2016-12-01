#![feature(plugin_registrar, quote, rustc_private)]

extern crate lalr;
extern crate redfa;
extern crate syntax;
extern crate rustc_plugin;

pub mod lexer;
pub mod parser;

use syntax::ext::base;
use syntax::symbol::Symbol;
use rustc_plugin as plugin;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut plugin::Registry) {
    reg.register_syntax_extension(Symbol::intern("parser"),
        base::SyntaxExtension::NormalTT(Box::new(parser::expand_parser), None, true));
    reg.register_syntax_extension(Symbol::intern("lexer"),
        base::SyntaxExtension::NormalTT(Box::new(lexer::expand_lexer), None, true));
}
