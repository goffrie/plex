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

You can find a demo in `examples/demo.rs`. Note that nightly Rust (> 2017-02-15) is required.

## Usage

First, include the plugin.

```rust
#![feature(plugin)]
#![plugin(plex)]
```

### Creating a lexer

To define a lexer, use the `lexer!` macro.

```rust
lexer! {
    fn take_token(tok: 'a) -> Token<'a>;
```

First declare the name of the function, the name of the token you will be able
to access within the lexer, and the return type of your lexer. You can also
optionally declare a lifetime for the strings you accept (here, `'a`).

Note that this will declare a function with the actual signature
`fn take_token<'a>(text: &mut &'a str) -> Option<Token<'a>>`. The lexer will
modify the `text` slice to remove the consumed text. This is designed to make
it easier to create an iterator of `Token`s out of a string slice.

```rust
    r"[ \t\r\n]" => Token::Whitespace,
    "[0-9]+" => Token::IntegerLiteral(tok.parse().unwrap()),
    r#""[^"]*""# => Token::StringLiteral(&tok[1..tok.len()-1]),
```

The rest of your lexer should consist of rules. The left hand side should be a
literal string (raw string literals are OK) corresponding to a regular
expression. You can use the typical regular expression syntax, including
parentheses for grouping, square brackets for character classes, and the usual
`.`, `|`, `*`, and `+`. (`?` is currently not supported.) You can also use
some extra operators, like `~` for negation and `&` for conjunction:

```rust
    r"/\*~(.*\*/.*)\*/" => Token::Comment(tok),
```

The above regular expression will match a C-style comment with `/* */`
delimiters, but won't allow `*/` to appear inside the comment. (`.*\*/.*`
matches any string containing `*/`, `~(.*\*/.*)` matches any string that does
not.) This is important because the lexer uses maximal munch. If you had
written simply `r"/\*.*\*/"`, then the lexer would consume the longest matching
substring.  That would interpret `/* comment */ not comment? /* comment */` as
one large comment.

```rust
    "let" => Token::Let,
    "[a-zA-Z]+" => Token::Ident(tok),
    "." => panic!("unexpected character"),
}
```

Note that if multiple rules could apply, the one declared first wins. This lets
you declare keywords (which have precedence over identifiers) by putting them
first.

### Creating a parser

`plex` uses the LALR(1) construction for parsers. This section, and `plex` in
general, will assume you understand LR parsing, along with its associated
vocabulary.

To define a parser, use the `parser!` macro.

```rust
parser! {
    fn parse(Token, Span);
```

This declares the name of the parser (in this case, `parse`) and the input
types that it takes. In this case, `parse` will take any iterator of pairs
`(Token, Span)`. The token type must be an `enum` whose variants are in scope.
(This is a current limitation of `plex` that might be fixed later.). Those
variants are the terminals of your grammar. `plex`-generated parsers also keep
track of source locations ("spans") that are fed into it, so you'll need to
mention your span type here. If you don't want to keep track of source
locations, you can use the unit type `()`.

Next, tell `plex` how to combine two spans:

```rust
    (a, b) {
        Span {
            lo: a.lo,
            hi: b.hi,
        }
    }
```

Here, `a` and `b` are `Span`s.  In this case we've defined `Span` as a
structure with two fields, `lo` and `hi`, representing the byte offsets of the
beginning and end of the span. Note that the extra braces are necessary here:
the body of the function has to be a block.

Now you write your grammar. For each nonterminal, write its name, together with
its type. This indicates the kind of data that the nonterminal parses into.

```rust
    statements: Vec<Expr> {
```

Note that the first nonterminal is special: it's the start symbol of your
grammar, and its type is the return type (more or less) of the parser.

Then write the rules for this nonterminal. (The left-hand side of each rule is
implied to be `statements`.)

```rust
        statements[mut st] expr[e] Semi => {
            st.push(e);
            st
        }
```

Write the rule's right-hand side, an arrow `=>`, and the code to handle this
rule. The right-hand side is a sequence of nonterminals or terminals to match.
Here, `statements` and `expr` are nonterminals. Square brackets assign a pattern
to the result of a nonterminal, allowing us to use the data returned by that
nonterminal. Terminals must be enum variants brought in scope. The expression
must evaluate to the type of the left-hand side: in this case, `Vec<Expr>`.

```rust
        => vec![],
    }
```

Empty rules are allowed: just don't write anything before the arrow.

If a terminal (i.e. a token) is a tuple-like enum variant, and so holds data,
you should destructure it using round brackets:

```
    expr: Expr {
        Ident(s) => Expr::Var(span!(), s)
    }
}
```

Inside a rule, the `span!()` macro evaluates to the span of the current
right-hand-side. However, this only works if at least one token was matched. If
the rule matched an empty sequence, `span!()` will panic, so avoid using it in
nullable rules.

The return type of this parser is
`Result<Vec<Expr>, (Option<(Token, Span)>, &'static str)>`. The error type is a
pair consisting of the unexpected token, or `None` for EOF, and a message
describing the tokens that were expected.
