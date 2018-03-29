use std::collections::{BTreeSet, VecDeque};
use std::char;

use redfa::Dfa;
use redfa::regex::Regex;

use syn;
use syn::buffer::Cursor;
use syn::synom::{PResult, Synom};
use syn::{Expr, Ident, Lifetime, LitStr, Type, Visibility};
use quote::Tokens;
use proc_macro2::{Delimiter, Span};
use proc_macro::TokenStream;

fn dfa_fn<T>(
    dfa: &Dfa<char, T>,
    state_enum: Ident,
    state_paths: &[Tokens],
    fn_name: Ident,
) -> Tokens {
    let mut arms = vec![];
    for (tr, state_name) in dfa.states.iter().zip(state_paths.iter().cloned()) {
        let mut subarms = vec![];
        let mut iter = tr.by_char.iter().peekable();
        while let Some((&ch, &target)) = iter.next() {
            let mut end = ch;
            while let Some(&(&nextc, &nextt)) = iter.peek() {
                if nextc as u32 != (end as u32) + 1 || nextt != target {
                    break;
                }
                end = nextc;
                iter.next();
            }
            let pat = if ch == end {
                quote!(#ch)
            } else {
                quote!(#ch ... #end)
            };
            let body = state_paths[target as usize].clone();
            subarms.push(quote!(#pat => #body));
        }
        let default_state = state_paths[tr.default as usize].clone();
        arms.push(quote!(#state_name => match ch {
            #(#subarms,)*
            _ => #default_state
        }));
    }
    quote! {
        fn #fn_name(state: #state_enum, ch: char) -> #state_enum {
            match state {
                #(#arms,)*
            }
        }
    }
}

fn first_nullable<T>(vec: &[Regex<T>]) -> Option<usize> {
    vec.iter().position(Regex::nullable)
}

fn dfa_make_names<V>(dfa: &Dfa<char, V>) -> Vec<String> {
    let mut names = vec![String::new(); dfa.states.len()];
    let mut seen = BTreeSet::new();
    seen.insert(0);
    let mut worklist = VecDeque::new();
    worklist.push_back((0, "S_".into()));
    while let Some((i, name)) = worklist.pop_front() {
        for (&c, &next) in &dfa.states[i as usize].by_char {
            if seen.insert(next) {
                let new_name = if c.is_alphanumeric() {
                    format!("{}{}", name, c)
                } else {
                    format!("{}_{:x}_", name, c as u32)
                };
                worklist.push_back((next, new_name));
            }
        }
        let default = dfa.states[i as usize].default;
        if seen.insert(default) {
            let new_name = format!("{}__", name);
            worklist.push_back((default, new_name));
        }
        names[i as usize] = name;
    }
    names
}

struct Rule {
    pattern: LitStr,
    expr: Expr,
}

fn parse_rules(mut input: Cursor) -> PResult<Vec<Rule>> {
    let mut rules = vec![];
    while !input.eof() {
        // FIXME: Make some nicer error messages, preferably when syn supports it.
        let (pattern, input_) = <LitStr as Synom>::parse(input)?;
        let (_, input_) = <Token![=>] as Synom>::parse(input_)?;
        // Like in a `match` expression, braced block doesn't require a comma before the next rule.
        let optional_comma = input_.group(Delimiter::Brace).is_some();
        let (expr, input_) = <Expr as Synom>::parse(input_)?;
        rules.push(Rule { pattern, expr });
        match <Token![,] as Synom>::parse(input_) {
            Ok((_, input_)) => {
                input = input_;
            }
            Err(e) => {
                input = input_;
                if !input.eof() && !optional_comma {
                    return Err(e);
                }
            }
        }
    }
    Ok((rules, input))
}

struct Lexer {
    vis: Visibility,
    name: Ident,
    input: Ident,
    lifetime: Option<Lifetime>,
    return_type: Type,
    rules: Vec<Rule>,
}

impl Synom for Lexer {
    named!(parse -> Self, do_parse!(
        vis: syn!(Visibility) >>
        keyword!(fn) >>
        name: syn!(Ident) >>
        input_and_lifetime: parens!(tuple!(
            syn!(Ident),
            option!(do_parse!(punct!(:) >> lt: syn!(Lifetime) >> (lt)))
        )) >>
        punct!(->) >>
        return_type: syn!(Type) >>
        punct!(;) >>
        rules: call!(parse_rules) >>
        ({
            let (_, (input, lifetime)) = input_and_lifetime;
            Lexer { vis, name, input, lifetime, return_type, rules }
        })
    ));
}

pub fn lexer(input: TokenStream) -> TokenStream {
    let Lexer {
        vis,
        name,
        input,
        lifetime,
        return_type,
        rules,
    } = syn::parse(input).unwrap_or_else(|e| {
        panic!("parse error: {:?}", e);
    });

    let (re_vec, actions): (Vec<Regex<_>>, Vec<Expr>) = rules
        .into_iter()
        .map(|Rule { pattern, expr }| {
            let re = match pattern.value().parse() {
                Ok(r) => r,
                Err(e) => {
                    pattern
                        .span
                        .unstable()
                        .error(format!("invalid regular expression: {}", e))
                        .emit();
                    Regex::Null // dummy
                }
            };
            if re.nullable() {
                pattern
                    .span
                    .unstable()
                    .error("token must not match the empty string")
                    .emit();
            }
            (re, expr)
        })
        .unzip();

    let (dfa, _) = Dfa::from_derivatives(vec![re_vec]);
    let dfa = dfa.map(|vec| first_nullable(&vec)).minimize().map(|&x| x);
    let error_state_ix = dfa.states.iter().enumerate().position(|(ix, state)| {
        state.value.is_none() && state.by_char.is_empty() && state.default as usize == ix
    });
    if error_state_ix.is_none() {
        Span::call_site()
            .unstable()
            .warning("this DFA has no error state; it will always scan the entire input")
            .emit();
    }

    // Construct "human-readable" names for each of the DFA states.
    // This is purely to make the generated code nicer.
    let mut names: Vec<Ident> = dfa_make_names(&dfa).into_iter().map(Ident::from).collect();
    // If we've identified an error state, give it the special name "Error".
    if let Some(ix) = error_state_ix {
        names[ix] = Ident::from("Error");
    }
    // The full paths to each of the state names (e.g. `State::Error`).
    let state_paths: Vec<Tokens> = names.iter().map(|name| quote!(State::#name)).collect();

    let initial_state = state_paths[0].clone();
    let error_state = error_state_ix.map(|ix| state_paths[ix].clone());

    // Construct the actual DFA transition function, which, given a `State` and the next character, returns the next `State`.
    let transition_fn = dfa_fn(
        &dfa,
        Ident::from("State"),
        &state_paths,
        Ident::from("transition"),
    );

    let accepting_fn = {
        let arms = dfa.states
            .iter()
            .map(|state| state.value)
            .zip(&state_paths)
            .filter_map(|(maybe_act, state)| {
                maybe_act.map(|act| {
                    let act = act as u32;
                    quote!(#state => Some(#act))
                })
            });
        quote!(fn accepting(state: State) -> Option<u32> {
            match state {
                #(#arms,)*
                _ => None
            }
        })
    };

    let compute_result = {
        let compute_arms = actions.into_iter().enumerate().map(|(i, expr)| {
            let i = i as u32;
            quote!(#i => #expr)
        });
        quote!(match which {
            #(#compute_arms,)*
            _ => unreachable!()
        })
    };
    quote!(
        #vis fn #name #(<#lifetime>)* (input: &#(#lifetime)* str) -> Option<(#return_type, &#(#lifetime)* str)> {
            #[derive(Copy, Clone)]
            #[allow(non_camel_case_types)]
            enum State {
                #(#names,)*
            }
            #transition_fn
            #accepting_fn
            let mut state = #initial_state;
            let mut remaining = input.char_indices();
            let mut last_match = None;
            loop {
                if let Some(which) = accepting(state) {
                    last_match = Some((which, remaining.clone()));
                }
                #( // only produce this if `error_state` exists.
                    if let #error_state = state {
                        break;
                    }
                )*
                if let Some((_, ch)) = remaining.next() {
                    state = transition(state, ch);
                } else {
                    break;
                }
            }
            if let Some((which, mut remaining)) = last_match {
                let ix = if let Some((ix, _)) = remaining.next() {
                    ix
                } else {
                    input.len()
                };
                let #input = &input[..ix];
                let rule_result = #compute_result;
                Some((rule_result, &input[ix..]))
            } else {
                None
            }
        }
    ).into()
}
