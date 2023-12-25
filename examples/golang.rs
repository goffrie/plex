//! A lexer and parser for Go, based on the Aug 2, 2023 version of https://go.dev/ref/spec

use std::io::Read;

mod lexer {
    use plex::lexer;

    #[derive(Debug, Copy, Clone)]
    pub enum Token {
        Newline,
        Whitespace, // non-newline
        Comment,

        Ident,

        // keywords
        Break,
        Case,
        Chan,
        Const,
        Continue,
        Default,
        Defer,
        Else,
        Fallthrough,
        For,
        Func,
        Go,
        Goto,
        If,
        Import,
        Interface,
        Map,
        Package,
        Range,
        Return,
        Select,
        Struct,
        Switch,
        Type,
        Var,

        // operators
        Plus,
        Minus,
        Times,
        Div,
        Mod,
        BitAnd,
        BitOr,
        BitXor,
        LShift,
        RShift,
        BitAndNot,
        PlusEquals,
        MinusEquals,
        TimesEquals,
        DivEquals,
        ModEquals,
        BitAndEquals,
        BitOrEquals,
        BitXorEquals,
        LShiftEquals,
        RShiftEquals,
        BitAndNotEquals,
        BoolAnd,
        BoolOr,
        LeftArrow,
        PlusPlus,
        MinusMinus,
        EqualsEquals,
        LessThan,
        GreaterThan,
        Equals,
        BoolNot,
        Tilde,
        NotEquals,
        LessEquals,
        GreaterEquals,
        Walrus,
        DotDotDot,
        LParen,
        RParen,
        LBracket,
        RBracket,
        LBrace,
        RBrace,
        Comma,
        Dot,
        Semi,
        Colon,

        IntLiteral,
        FloatLiteral,
        ImaginaryLiteral,
        RuneLiteral,
        StringLiteral,

        Error,
    }

    lexer! {
        fn next_token(text: 'a) -> Token;
        r"\n" => Token::Newline,
        r"[ \t\r]+" => Token::Whitespace,
        // "General comments" (/* .. */) - can't contain "*/"
        r"/[*](~(.*[*]/.*))[*]/" => Token::Comment,
        // "Line comments" (// ...)
        r"//[^\n]*" => Token::Comment,

        r"break" => Token::Break,
        r"case" => Token::Case,
        r"chan" => Token::Chan,
        r"const" => Token::Const,
        r"continue" => Token::Continue,
        r"default" => Token::Default,
        r"defer" => Token::Defer,
        r"else" => Token::Else,
        r"fallthrough" => Token::Fallthrough,
        r"for" => Token::For,
        r"func" => Token::Func,
        r"go" => Token::Go,
        r"goto" => Token::Goto,
        r"if" => Token::If,
        r"import" => Token::Import,
        r"interface" => Token::Interface,
        r"map" => Token::Map,
        r"package" => Token::Package,
        r"range" => Token::Range,
        r"return" => Token::Return,
        r"select" => Token::Select,
        r"struct" => Token::Struct,
        r"switch" => Token::Switch,
        r"type" => Token::Type,
        r"var" => Token::Var,

        // TODO: support Unicode identifiers (this is annoying since redfa doesn't support \u syntax)
        r"[a-zA-Z_][a-zA-Z0-9_]*" => Token::Ident,

        r"\+" => Token::Plus,
        r"-" => Token::Minus,
        r"\*" => Token::Times,
        r"/" => Token::Div,
        r"%" => Token::Mod,
        r"\&" => Token::BitAnd,
        r"\|" => Token::BitOr,
        r"^" => Token::BitXor,
        r"<<" => Token::LShift,
        r">>" => Token::RShift,
        r"\&^" => Token::BitAndNot,
        r"\+=" => Token::PlusEquals,
        r"-=" => Token::MinusEquals,
        r"\*=" => Token::TimesEquals,
        r"/=" => Token::DivEquals,
        r"%=" => Token::ModEquals,
        r"\&=" => Token::BitAndEquals,
        r"\|=" => Token::BitOrEquals,
        r"^=" => Token::BitXorEquals,
        r"<<=" => Token::LShiftEquals,
        r">>=" => Token::RShiftEquals,
        r"\&^=" => Token::BitAndNotEquals,
        r"\&\&" => Token::BoolAnd,
        r"\|\|" => Token::BoolOr,
        r"<-" => Token::LeftArrow,
        r"\+\+" => Token::PlusPlus,
        r"--" => Token::MinusMinus,
        r"==" => Token::EqualsEquals,
        r"<" => Token::LessThan,
        r">" => Token::GreaterThan,
        r"=" => Token::Equals,
        r"!" => Token::BoolNot,
        r"\~" => Token::Tilde,
        r"!=" => Token::NotEquals,
        r"<=" => Token::LessEquals,
        r">=" => Token::GreaterEquals,
        r":=" => Token::Walrus,
        r"\.\.\." => Token::DotDotDot,
        r"\(" => Token::LParen,
        r"\)" => Token::RParen,
        r"\[" => Token::LBracket,
        r"\]" => Token::RBracket,
        r"{" => Token::LBrace,
        r"}" => Token::RBrace,
        r"," => Token::Comma,
        r"\." => Token::Dot,
        r";" => Token::Semi,
        r":" => Token::Colon,

        r"=" => Token::Equals,
        r"\+" => Token::Plus,
        r"-" => Token::Minus,
        r"\*" => Token::Times,
        r"/" => Token::Div,
        r"\(" => Token::LParen,
        r"\)" => Token::RParen,
        r";" => Token::Semi,

        // decimal
        r"0|[1-9](_?[0-9])*" => Token::IntLiteral,
        // binary
        r"0[bB](_?[0-1])*" => Token::IntLiteral,
        // octal
        r"0[oO](_?[0-7])*" => Token::IntLiteral,
        // hex
        r"0[xX](_?[0-9a-fA-F])*" => Token::IntLiteral,

        // decimal
        // TODO: this somehow panics
        // r"[0-9](_?[0-9])*\.([0-9](_?[0-9])*)?([eE][-+]?[0-9](_?[0-9])*)?" => Token::FloatLiteral,
        // hex
        r"0[xX](_?[0-9a-fA-F])*(\.([0-9a-fA-F](_?[0-9a-fA-F])*)?)?[pP][-+]?[0-9](_?[0-9])*" => Token::FloatLiteral,

        // imaginary literal
        r"[0-9](_?[0-9])*i" => Token::ImaginaryLiteral, // TODO: this is wrong

        // rune literal
        r"'[^']*'|'\\''" => Token::RuneLiteral,

        // string literal
        r#"\"[^"]*\""# => Token::StringLiteral, // TODO: this is wrong

        r#"."# => Token::Error,
    }

    pub struct Lexer<'a> {
        original: &'a str,
        remaining: &'a str,
        last_token: Option<Token>,
    }

    impl<'a> Lexer<'a> {
        pub fn new(s: &'a str) -> Lexer<'a> {
            Lexer {
                original: s,
                remaining: s,
                last_token: None,
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub struct Span {
        pub lo: usize,
        pub hi: usize,
    }

    impl<'a> Iterator for Lexer<'a> {
        type Item = (Token, Span);
        fn next(&mut self) -> Option<(Token, Span)> {
            let token = loop {
                let (tok, span) = if let Some((tok, new_remaining)) = next_token(self.remaining) {
                    let lo = self.original.len() - self.remaining.len();
                    let hi = self.original.len() - new_remaining.len();
                    self.remaining = new_remaining;
                    (tok, Span { lo, hi })
                } else {
                    return None;
                };
                match tok {
                    Token::Whitespace | Token::Comment => {
                        continue;
                    }
                    Token::Newline => match self.last_token {
                        Some(
                            Token::Ident
                            | Token::IntLiteral
                            | Token::FloatLiteral
                            | Token::ImaginaryLiteral
                            | Token::RuneLiteral
                            | Token::StringLiteral
                            | Token::Break
                            | Token::Continue
                            | Token::Fallthrough
                            | Token::Return
                            | Token::PlusPlus
                            | Token::MinusMinus
                            | Token::RParen
                            | Token::RBracket
                            | Token::RBrace,
                        ) => break Some((Token::Semi, span)),
                        _ => (),
                    },
                    tok => {
                        break Some((tok, span));
                    }
                }
            };
            self.last_token = token.map(|(tok, _)| tok);
            token
        }
    }
}

mod ast {
    use crate::lexer::Span;
    #[derive(Debug)]
    pub struct SourceFile {
        pub span: Span,
    }
}

mod parser {
    use crate::ast::*;
    use crate::lexer::Token::*;
    use crate::lexer::*;
    use plex::parser;
    parser! {
        fn parse_(Token, Span);

        // combine two spans
        (a, b) {
            Span {
                lo: a.lo,
                hi: b.hi,
            }
        }

        // Packages

        // Source file organization
        source_file: SourceFile {
            package_clause Semi import_decls top_level_decls => SourceFile {
                span: span!(),
            }
        }

        // Package clause
        package_clause: () {
            Package Ident => ()
        }
        package_name: () {
            Ident => (),
        }

        // Import declarations
        import_decls: () {
            => (),
            import_decls import_decl Semi => (),
        }
        import_decl: () {
            Import import_spec => (),
            Import LParen import_specs RParen => (),
            // allow missing semi before rparen
            Import LParen import_specs import_spec RParen => (),
        }
        import_spec: () {
            Dot import_path => (),
            Ident import_path => (),
            import_path => (),
        }
        import_path: () {
            StringLiteral => (),
        }
        import_specs: () {
            => (),
            import_specs import_spec Semi => (),
        }

        top_level_decls: () {
            => (),
            top_level_decls top_level_decl Semi => (),
        }
        top_level_decl: () {
            declaration => (),
            function_decl => (),
            // method_decl => (),
        }
        declaration: () {
            const_decl => (),
            type_decl => (),
            var_decl => (),
        }

        // Function declarations
        function_decl: () {
            Func Ident signature => (),
            Func Ident type_parameters signature => (),
            Func Ident signature block => (),
            Func Ident type_parameters signature block => (),
        }

        // Blocks
        block: () {
            LBrace statement_list RBrace => (),
            // allow missing semi before rbrace
            LBrace statement_list Semi statement RBrace => (),
        }
        statement_list: () {
            => (),
            statement_list statement Semi => (),
        }

        // Constant declarations
        const_decl: () {
            Const const_spec => (),
            Const LParen const_specs RParen => (),
            // allow missing semi before rparen
            Const LParen const_specs const_spec RParen => (),
        }
        const_specs: () {
            => (),
            const_specs const_spec Semi => (),
        }
        const_spec: () {
            identifier_list => (),
            identifier_list Equals expression_list => (),
            identifier_list type_ Equals expression_list => (),
        }
        expression_list: () {
            expression => (),
            expression_list Comma expression => (),
        }

        type_decl: () {
            Type type_spec => (),
            Type LParen type_specs RParen => (),
            // allow missing semi before rparen
            Type LParen type_specs type_spec RParen => (),
        }
        type_specs: () {
            => (),
            type_specs type_spec Semi => (),
        }
        type_spec: () {
            // alias
            Ident Equals type_ => (),
            // type definition
            Ident type_ => (),
            Ident type_parameters type_ => (),
        }

        type_parameters: () {
            LBracket type_param_list RBracket => (),
            LBracket type_param_list Comma RBracket => (),
        }
        type_param_list: () {
            type_param_decl => (),
            type_param_list Comma type_param_decl => (),
        }
        type_param_decl: () {
            identifier_list type_constraint => (),
        }

        type_constraint: () {
            type_elem => (),
        }

        // Variable declarations
        var_decl: () {
            Var var_spec => (),
            Var LParen var_specs RParen => (),
            // allow missing semi before rparen
            Var LParen var_specs var_spec RParen => (),
        }
        var_specs: () {
            => (),
            var_specs var_spec Semi => (),
        }
        var_spec: () {
            identifier_list type_ => (),
            identifier_list type_ Equals expression_list => (),
            identifier_list Equals expression_list => (),
        }

        // Types
        type_not_parens: () {
            // type name
            Ident => (),
            qualified_ident => (),
            Ident type_args => (),
            qualified_ident type_args => (),
            type_lit => (),
        }
        type_: () {
            type_not_parens => (),
            LParen type_ RParen => (),
        }
        type_name: () {
            Ident => (),
            qualified_ident => (),
        }
        type_args: () {
            LBracket type_list RBracket => (),
            LBracket type_list Comma RBracket => (),
        }
        type_list: () {
            type_ => (),
            type_list Comma type_ => (),
        }
        type_lit: () {
            array_type => (),
            struct_type => (),
            pointer_type => (),
            function_type => (),
            interface_type => (),
            slice_type => (),
            map_type => (),
            channel_type => (),
        }

        // Array types
        array_type: () {
            LBracket expression RBracket type_ => (),
        }
        
        // Slice types
        slice_type: () {
            LBracket RBracket type_ => (),
        }

        // Struct types
        struct_type: () {
            Struct LBrace field_decls RBrace => (),
            // allow missing semi before rbrace
            Struct LBrace field_decls field_decl RBrace => (),
        }
        field_decls: () {
            => (),
            field_decls field_decl Semi => (),
        }
        field_decl: () {
            identifier_list type_ => (),
            identifier_list type_ StringLiteral => (),
            embedded_field => (),
            embedded_field StringLiteral => (),
        }
        embedded_field: () {
            type_name => (),
            Times type_name => (),
            type_name type_args => (),
            Times type_name type_args => (),
        }

        // Pointer types
        pointer_type: () {
            Times type_ => (),
        }
        
        // Function types
        function_type: () {
            Func signature => (),
        }
        signature: () {
            parameters => (),
            parameters result => (),
        }
        result: () {
            parameters => (),
            type_not_parens => (),
        }
        parameters: () {
            LParen RParen => (),
            LParen parameter_list RParen => (),
            LParen parameter_list Comma RParen => (),
        }
        parameter_list: () {
            parameter_decl => (),
            parameter_list Comma parameter_decl => (),
        }
        parameter_decl: () {
            #[overriding] // This resolves a conflict between `type_` and `identifier_list`.
            Ident => (),
            type_ => (),
            parameter_identifier_list type_ => (),
            DotDotDot type_ => (),
            identifier_list DotDotDot type_ => (),
        }
        parameter_identifier_list: () {
            #[no_reduce(LBracket)] // TODO: not sure about this
            Ident => (),
            parameter_identifier_list Comma Ident => (),
        }

        // Interface types
        interface_type: () {
            Interface LBrace interface_elems RBrace => (),
            // allow missing semi before rbrace
            Interface LBrace interface_elems interface_elem RBrace => (),
        }
        interface_elems: () {
            => (),
            interface_elems interface_elem Semi => (),
        }
        interface_elem: () {
            // method elem
            Ident signature => (),
            type_elem => (),
        }
        type_elem: () {
            type_term => (),
            // TODO: probably rename BitOr...
            type_elem BitOr type_term => (),
        }
        type_term: () {
            type_ => (),
            // underlying type
            Tilde type_ => (),
        }
        
        // Map types
        map_type: () {
            Map LBracket type_ RBracket type_ => (),
        }

        // Channel types
        channel_type: () {
            // Resolve ambiguity in `chan <- chan` by associating the `<-` with the left-most `chan`
            // TODO: make sure this doesn't do anything else bad
            #[overriding]
            Chan type_ => (),
            Chan LeftArrow type_ => (),
            LeftArrow Chan type_ => (),
        }

        identifier_list: () {
            // #[no_reduce(LBracket)] // TODO: not sure about this
            Ident => (),
            identifier_list Comma Ident => (),
        }
        // function_decl: () {
        // }
        // method_decl: () {
        // }

        // Expressions

        // Operands
        operand: () {
            literal => (),
            Ident => (),
            Ident type_args => (),
            qualified_ident => (),
            qualified_ident type_args => (),
            LParen expression RParen => (),
        }
        literal: () {
            // basic literals
            IntLiteral => (),
            FloatLiteral => (),
            ImaginaryLiteral => (),
            RuneLiteral => (),
            StringLiteral => (),
            // composite literals
            // literal_type literal_value => (),
        }

    
        // Function literals
        function_lit: () {
            Func signature block => (),
        }

        // Primary expressions
        primary_expr: () {
            operand => (),
            // ...
        }

        unary_expr: () {
            primary_expr => (),
            unary_op unary_expr => (),
        }
        unary_op: () {
            Plus => (),
            Minus => (),
            BoolNot => (),
            BitXor => (),
            Times => (),
            BitAnd => (),
            LeftArrow => (),
        }

        expression: () {
            unary_expr => (),
            // expression binary_op expression => (),
        }

        qualified_ident: () {
            Ident Dot Ident => (),
        }

        // Statements
        statement: () {
            declaration => (),
            // ...
        }
    }

    pub fn parse<I: Iterator<Item = (Token, Span)>>(
        i: I,
    ) -> Result<SourceFile, (Option<(Token, Span)>, &'static str)> {
        parse_(i)
    }
}

fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let lexer = lexer::Lexer::new(&s).inspect(|tok| eprintln!("tok: {:?}", tok));
    let source_file = parser::parse(lexer).unwrap();
    println!("{:?}", source_file);
}
