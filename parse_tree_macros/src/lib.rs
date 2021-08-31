#![allow(unused_imports)]
use ::proc_macro::TokenStream;
use ::proc_macro2::{Span, TokenStream as TokenStream2};
use ::quote::{quote, quote_spanned, ToTokens};
use ::syn::{
    parse::{self, Parse, ParseStream, Parser},
    punctuated::Punctuated,
    Result, *,
};
use syn::token::Impl;

// Thanks to discord user Yandros(MemeOverloard) for doing the bulk of the work with this
// macro
#[proc_macro_attribute]
pub fn trace_parser(attrs: TokenStream, input: TokenStream) -> TokenStream {
    parse_macro_input!(attrs as parse::Nothing);
    let mut input = parse_macro_input!(input as ImplItemMethod);
    let block = &mut input.block;

    let function_name = format!("{}", input.sig.ident);

    *block = parse_quote!({
        self.parse_stack.push(ParseStackEntry::Enter(#function_name.to_string()));
        let ret: Result<_> = (|| #block)();
        if let Err(e) = &ret {
            self.parse_stack.push(ParseStackEntry::ExitWithError(e.clone()));
        }
        else {
            self.parse_stack.push(ParseStackEntry::Exit);
        }
        ret
    });
    input.into_token_stream().into()
}

#[proc_macro_attribute]
pub fn trace_typechecker(attrs: TokenStream, input: TokenStream) -> TokenStream {
    parse_macro_input!(attrs as parse::Nothing);
    let mut input = parse_macro_input!(input as ImplItemMethod);
    let block = &mut input.block;

    let function_name = format!("{}", input.sig.ident);

    *block = parse_quote!({
        self.trace_stack.push(TraceStack::Enter(#function_name.to_string()));
        let ret: Result<_> = (|| #block)();
        self.trace_stack.push(TraceStack::Exit);
        ret
    });
    input.into_token_stream().into()
}

#[proc_macro_attribute]
pub fn local_impl(attrs: TokenStream, input: TokenStream) -> TokenStream {
    parse_macro_input!(attrs as parse::Nothing);

    let input = parse_macro_input!(input as ItemImpl);

    let trait_name = input.trait_.clone().unwrap().1;

    let method_heads = input
        .items
        .iter()
        .map(|item| match item {
            ImplItem::Method(ImplItemMethod { attrs, sig, .. }) => {
                quote! {
                    #(#attrs)*
                    #sig;
                }
            }
            _ => panic!("Only methods are allowed"),
        })
        .collect::<Vec<_>>();

    let trait_def = quote!(
        trait #trait_name {
            #(#method_heads)*
        }
    );

    quote!(
        #input
        #trait_def
    )
    .into_token_stream()
    .into()
}
