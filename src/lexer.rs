use std::char;
use std::collections::{BTreeSet, VecDeque};

use redfa::regex::Regex;
use redfa::Dfa;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{
    parenthesized, parse_macro_input, token, Error, Expr, Ident, Lifetime, LitStr, Token, Type,
    Visibility,
};

fn dfa_fn<T>(
    dfa: &Dfa<char, T>,
    state_enum: Ident,
    state_paths: &[TokenStream],
    fn_name: Ident,
) -> TokenStream {
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

fn parse_rules(input: ParseStream) -> syn::Result<Vec<Rule>> {
    let mut rules = vec![];
    while !input.is_empty() {
        // FIXME: Make some nicer error messages.
        let pattern = input.parse()?;
        input.parse::<Token![=>]>()?;
        // Like in a `match` expression, braced block doesn't require a comma before the next rule.
        let optional_comma = input.peek(token::Brace);
        let expr = input.parse()?;
        rules.push(Rule { pattern, expr });
        match input.parse::<Token![,]>() {
            Ok(_) => {}
            Err(e) => {
                if !input.is_empty() && !optional_comma {
                    return Err(e);
                }
            }
        }
    }
    Ok(rules)
}

struct Lexer {
    vis: Visibility,
    name: Ident,
    input: Ident,
    lifetime: Option<Lifetime>,
    return_type: Type,
    rules: Vec<Rule>,
}

impl Parse for Lexer {
    fn parse(input: ParseStream) -> syn::Result<Lexer> {
        let lifetime;
        Ok(Lexer {
            vis: input.parse()?,
            name: {
                input.parse::<Token![fn]>()?;
                input.parse()?
            },
            input: {
                let inner;
                parenthesized!(inner in input);
                let lexer_input = inner.parse()?;
                if !inner.is_empty() {
                    inner.parse::<Token![:]>()?;
                    lifetime = Some(inner.parse()?);
                    if !inner.is_empty() {
                        return Err(inner.error("unexpected token after input lifetime"));
                    }
                } else {
                    lifetime = None;
                }
                lexer_input
            },
            lifetime,
            return_type: {
                input.parse::<Token![->]>()?;
                let t = input.parse()?;
                input.parse::<Token![;]>()?;
                t
            },
            rules: parse_rules(input)?,
        })
    }
}

pub fn lexer(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let Lexer {
        vis,
        name,
        input,
        lifetime,
        return_type,
        rules,
    } = parse_macro_input!(input as Lexer);

    let mut errors = vec![];
    let (re_vec, actions): (Vec<Regex<_>>, Vec<Expr>) = rules
        .into_iter()
        .map(|Rule { pattern, expr }| {
            let re = match pattern.value().parse() {
                Ok(r) => r,
                Err(e) => {
                    errors.push(Error::new_spanned(
                        &pattern,
                        format!("invalid regular expression: {}", e),
                    ));
                    Regex::Null // dummy
                }
            };
            if re.nullable() {
                errors.push(Error::new_spanned(
                    &pattern,
                    "token must not match the empty string",
                ));
            }
            (re, expr)
        })
        .unzip();

    let (dfa, _) = Dfa::from_derivatives(vec![re_vec]);
    let dfa = dfa.map(|vec| first_nullable(&vec)).minimize().map(|&x| x);
    let error_state_ix = dfa.states.iter().enumerate().position(|(ix, state)| {
        state.value.is_none() && state.by_char.is_empty() && state.default as usize == ix
    });
    // TODO: consider making this opt-out
    if error_state_ix.is_none() {
        errors.push(Error::new(
            Span::call_site(),
            "this DFA has no error state; it will always scan the entire input",
        ));
    }

    // Construct "human-readable" names for each of the DFA states.
    // This is purely to make the generated code nicer.
    let mut names: Vec<Ident> = dfa_make_names(&dfa)
        .into_iter()
        .map(|n| Ident::new(&n, Span::call_site()))
        .collect();
    // If we've identified an error state, give it the special name "Error".
    if let Some(ix) = error_state_ix {
        names[ix] = Ident::new("Error", Span::call_site());
    }
    // The full paths to each of the state names (e.g. `State::Error`).
    let state_paths: Vec<TokenStream> = names.iter().map(|name| quote!(State::#name)).collect();

    let initial_state = state_paths[0].clone();
    let error_state = error_state_ix.map(|ix| state_paths[ix].clone());

    // Construct the actual DFA transition function, which, given a `State` and the next character, returns the next `State`.
    let transition_fn = dfa_fn(
        &dfa,
        Ident::new("State", Span::call_site()),
        &state_paths,
        Ident::new("transition", Span::call_site()),
    );

    let accepting_fn = {
        let arms = dfa
            .states
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

    let l1 = lifetime.iter();
    let l2 = lifetime.iter();
    let l3 = lifetime.iter();

    let error_state = error_state.iter();
    let errors = errors.into_iter().map(|e| e.into_compile_error()).collect::<TokenStream>();

    quote!(
        #errors
        #vis fn #name #(<#l1>)* (input: &#(#l2)* str) -> Option<(#return_type, &#(#l3)* str)> {
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
    )
    .into()
}
