use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{any, choice, just, nested_delimiters, recursive, via_parser};
use chumsky::{select, IterParser, Parser};

use crate::driver::CRATE_STR;
use crate::error::{Error, Span};
use crate::lexer::Token;
use crate::str::{FunctionName, Identifier, ModuleName, SymbolName};
use crate::types::AliasedType;

use super::super::{
    ConstDecl, EnumDeclaration, Expression, Function, FunctionParam, Item, Module, Program,
    TypeAlias, UseDecl, UseItems, Visibility,
};
use super::{delimited_with_recovery, parse_token_with_recovery, ChumskyParse, ParseError};

impl ChumskyParse for Program {
    /// Parses a sequence of top-level [`Item`]s into a complete [`Program`].
    ///
    /// If an invalid item is encountered, it will safely skip the broken tokens
    /// until it finds a synchronization point. This prevents the parser from
    /// failing completely, allowing it to report multiple syntax errors across the file
    /// while substituting the unparseable sections with [`Item::Ignored`].
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let skip_until_next_item = any()
            .then(
                any()
                    .filter(|t| {
                        !matches!(
                            t,
                            Token::Pub
                                | Token::Use
                                | Token::Fn
                                | Token::Type
                                | Token::Mod
                                | Token::Enum
                                | Token::Const
                        )
                    })
                    .repeated(),
            )
            .map_with(|_, _| Item::Ignored);

        Item::parser()
            .recover_with(via_parser(skip_until_next_item))
            .repeated()
            .collect::<Vec<Item>>()
            .map_with(|items, e| Program {
                items: Arc::from(items),
                span: e.span(),
            })
    }
}

impl ChumskyParse for Item {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|item| {
            let func_parser = Function::parser().map(Item::Function);
            let type_parser = TypeAlias::parser().map(Item::TypeAlias);
            let use_parser = UseDecl::parser().map(Item::Use);
            let enum_parser = EnumDeclaration::parser().map(Item::EnumDeclaration);
            let const_parser = ConstDecl::parser().map(Item::Const);

            // Lazy item here
            let mod_parser = Module::parser_with_items(item).map(Item::Module);

            choice((
                func_parser,
                use_parser,
                type_parser,
                enum_parser,
                const_parser,
                mod_parser,
            ))
        })
    }
}

impl ChumskyParse for Function {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default)
            .labelled("function visibility");

        let params = delimited_with_recovery(
            FunctionParam::parser()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<_>>(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(Arc::from)
        .labelled("function parameters");

        let ret = just(Token::Arrow)
            .ignore_then(AliasedType::parser())
            .or_not()
            .labelled("return type");

        let body = just(Token::LBrace)
            .rewind()
            .ignore_then(Expression::parser())
            .recover_with(via_parser(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                Expression::empty,
            )))
            .labelled("function body");

        visibility
            .then_ignore(just(Token::Fn))
            .then(FunctionName::parser())
            .then(params)
            .then(ret)
            .then(body)
            .map_with(|((((visibility, name), params), ret), body), e| Self {
                visibility,
                name,
                params,
                ret,
                body,
                span: e.span(),
            })
    }
}

impl ChumskyParse for UseDecl {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default);

        let first_segment = select! {
            Token::Ident(ident) => Identifier::from_str_unchecked(ident),
            Token::Crate => Identifier::from_str_unchecked(CRATE_STR),
        };

        // Parse the base path prefix (e.g., `dependency_root_path::file::`, `dependency_root_path::dir::file::`,
        // or `crate::dir::file::`). We require at least 2 segments here because a valid import needs a minimum
        // of 3 items total: the dependency root path (or `crate`), the file, and the specific item.
        //
        // With the introduction of `mod` keyword and single-file flattening, 2 total segments are now
        // valid: `crate::item`, where `crate` is the program root.
        let path = first_segment
            .then_ignore(just(Token::DoubleColon))
            .then(
                Identifier::parser()
                    .then_ignore(just(Token::DoubleColon))
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map(|(first, mut rest)| {
                let mut path = vec![first];
                path.append(&mut rest);
                path
            });

        let aliased_item =
            SymbolName::parser().then(just(Token::As).ignore_then(SymbolName::parser()).or_not());

        let list = aliased_item
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(UseItems::List);
        let single = aliased_item.map(UseItems::Single);
        let items = choice((list, single));

        visibility
            .then_ignore(just(Token::Use))
            .then(path)
            .then(items)
            .then_ignore(just(Token::Semi))
            .map_with(|((visibility, path), items), e| Self {
                visibility,
                path,
                items,
                span: e.span(),
            })
    }
}

impl ChumskyParse for ConstDecl {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default);

        visibility
            .then_ignore(just(Token::Const))
            .then(Identifier::parser())
            .then_ignore(just(Token::Colon))
            .then(AliasedType::parser())
            .then_ignore(parse_token_with_recovery(Token::Eq))
            .then(Expression::parser())
            .then_ignore(just(Token::Semi))
            .map_with(|(((visibility, name), ty), expr), e| Self {
                visibility,
                name,
                ty,
                expr,
                span: e.span(),
            })
    }
}

impl ChumskyParse for FunctionParam {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let identifier = Identifier::parser();

        let ty = AliasedType::parser();

        identifier
            .then_ignore(just(Token::Colon))
            .then(ty)
            .map_with(|(identifier, ty), e| Self {
                identifier,
                ty,
                span: e.span(),
            })
    }
}

impl Module {
    pub fn parser_with_items<'tokens, 'src: 'tokens, I>(
        item_parser: impl Parser<'tokens, I, Item, ParseError<'src>> + Clone + 'tokens,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(Option::unwrap_or_default);

        let name = ModuleName::parser().map_with(|name, e| (name, e.span()));

        let items = item_parser
            .repeated()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .recover_with(via_parser(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                |_| Vec::new(),
            )))
            .map(Arc::from);

        visibility
            .then(just(Token::Mod).ignore_then(name).then(items))
            .map_with(|(visibility, (name, items)), e| Self {
                visibility,
                name: name.0,
                items,
                span: e.span(),
            })
            .validate(|module, _, emit| {
                // TODO: Enums may only be declared at the top level of a file (done so to reduce scope of the PR).
                // The bare name is the enum's identity in the ABI, and a module path would obscure it.
                // Direct children suffice. Nested modules validate their own items.
                for item in module.items.iter() {
                    if let Item::EnumDeclaration(decl) = item {
                        emit.emit(
                            Error::Grammar {
                                msg: format!(
                                    "enum `{}` is declared inside `mod {}`; enums may \
                                     only be declared at the top level of a file",
                                    decl.name(),
                                    module.name
                                ),
                            }
                            .with_span(decl.into()),
                        );
                    }
                }
                module
            })
    }
}
