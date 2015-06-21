## plex, a parser and lexer generator

[![Build Status](https://travis-ci.org/goffrie/plex.png)](https://travis-ci.org/goffrie/plex)

This crate provides a couple syntax extensions:

- `lexer!`, which creates a DFA-based lexer that uses maximal munch.  It works
  a bit like the `lex` tool.  You write regular expressions defining your
  tokens, together with Rust expressions that create your tokens from slices of
  input.
- `parser!`, which creates an LALR(1) parser.  It works a bit like `yacc`.  You
  write a context-free grammar, together with expressions for each rule.  You
  give each nonterminal a Rust type, allowing you to build an AST recursively.
  It also supports spans, giving you convenient source location reporting.

You can find a demo in `src/bin/demo.rs`.
