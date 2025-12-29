use chumsky::prelude::*;
use std::fmt;

pub type Span = SimpleSpan;
pub type Spanned<T> = (T, Span);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Token<'src> {
    // Keywords
    Fn,
    Let,
    Type,
    Mod,
    Const,
    Match,

    // Control symbols
    Arrow,
    Colon,
    Semi,
    Comma,
    Eq,
    FatArrow,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    AngleOpen,
    AngleClose,

    // Number literals
    DecLiteral(&'src str),
    HexLiteral(&'src str),
    BinLiteral(&'src str),

    // Boolean literal
    Bool(bool),

    // Identifier
    Ident(&'src str),

    // Jets, witnesses, and params
    Jet(&'src str),
    Witness(&'src str),
    Param(&'src str),

    // Built-in types (List, Option, Either)
    BuiltinType(&'src str),

    // Unsigned integer types
    UnsignedType(&'src str),

    // Boolean type
    BooleanType,

    // Built-in functions
    BuiltinFn(&'src str),

    // Built-in aliases
    BuiltinAlias(&'src str),

    // Comments and block comments
    //
    // We would discard them for the compiler, but they are needed, for example, for the formatter.
    Comment,
    BlockComment,
}

impl<'src> fmt::Display for Token<'src> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Fn => write!(f, "fn"),
            Token::Let => write!(f, "let"),
            Token::Type => write!(f, "type"),
            Token::Mod => write!(f, "mod"),
            Token::Const => write!(f, "const"),
            Token::Match => write!(f, "match"),

            Token::Arrow => write!(f, "->"),
            Token::Colon => write!(f, ":"),
            Token::Semi => write!(f, ";"),
            Token::Comma => write!(f, ","),
            Token::Eq => write!(f, "="),
            Token::FatArrow => write!(f, "=>"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::AngleOpen => write!(f, "<"),
            Token::AngleClose => write!(f, ">"),

            Token::DecLiteral(s) | Token::HexLiteral(s) | Token::BinLiteral(s) => {
                write!(f, "{}", s)
            }

            Token::Ident(s) => write!(f, "{}", s),

            Token::Jet(s) => write!(f, "jet::{}", s),
            Token::Witness(s) => write!(f, "witness::{}", s),
            Token::Param(s) => write!(f, "param::{}", s),

            Token::BuiltinType(s) => write!(f, "{}", s),
            Token::UnsignedType(s) => write!(f, "{}", s),
            Token::BuiltinFn(s) => write!(f, "{}", s),
            Token::BuiltinAlias(s) => write!(f, "{}", s),

            Token::BooleanType => write!(f, "bool"),
            Token::Bool(b) => write!(f, "{}", b),

            Token::Comment => write!(f, "comment"),
            Token::BlockComment => write!(f, "block_comment"),
        }
    }
}

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, Span>>> {
    let num = text::int(10).map(Token::DecLiteral);
    let hex = just("0x").ignore_then(text::int(16)).map(Token::HexLiteral);
    let bin = just("0b").ignore_then(text::int(2)).map(Token::BinLiteral);

    let macros = choice((just("assert!"), just("panic!"), just("dbg!"))).map(Token::BuiltinFn);

    let keyword = text::ident().map(|s| match s {
        "fn" => Token::Fn,
        "let" => Token::Let,
        "type" => Token::Type,
        "mod" => Token::Mod,
        "const" => Token::Const,
        "match" => Token::Match,
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        "List" | "Either" | "Option" => Token::BuiltinType(s),
        "u1" | "u2" | "u4" | "u8" | "u16" | "u32" | "u64" | "u128" | "u256" => {
            Token::UnsignedType(s)
        }
        "bool" => Token::BooleanType,
        "unwrap_left" | "unwrap_right" | "array_fold" | "for_while" | "is_none" | "unwrap"
        | "into" | "fold" => Token::BuiltinFn(s),
        "Ctx8" | "Pubkey" | "Message64" | "Message" | "Signature" | "Scalar" | "Fe" | "Gej"
        | "Ge" | "Point" | "Height" | "Time" | "Distance" | "Duration" | "Lock" | "Outpoint"
        | "Confidential1" | "ExplicitAsset" | "Asset1" | "ExplicitAmount" | "Amount1"
        | "ExplicitNonce" | "Nonce" | "TokenAmount1" => Token::BuiltinAlias(s),
        _ => Token::Ident(s),
    });

    let jet = just("jet::")
        .ignore_then(text::ident())
        .map(Token::Jet)
        .labelled("jet");
    let witness = just("witness::")
        .labelled("witness")
        .ignore_then(text::ident())
        .map(Token::Witness);
    let param = just("param::")
        .ignore_then(text::ident())
        .map(Token::Param)
        .labelled("param");

    let op = choice((
        just("->").to(Token::Arrow),
        just("=>").to(Token::FatArrow),
        just("=").to(Token::Eq),
        just(":").to(Token::Colon),
        just(";").to(Token::Semi),
        just(",").to(Token::Comma),
        just("(").to(Token::LParen),
        just(")").to(Token::RParen),
        just("[").to(Token::LBracket),
        just("]").to(Token::RBracket),
        just("{").to(Token::LBrace),
        just("}").to(Token::RBrace),
        just("<").to(Token::AngleOpen),
        just(">").to(Token::AngleClose),
    ));

    let comment = just("//")
        .ignore_then(any().and_is(just('\n').not()).repeated())
        .to(Token::Comment);

    let block_comment = just("/*")
        .ignore_then(just("*/").not().then(any()).repeated())
        .then_ignore(just("*/"))
        .to(Token::BlockComment);

    let token = choice((
        comment,
        block_comment,
        jet,
        witness,
        param,
        macros,
        keyword,
        hex,
        bin,
        num,
        op,
    ));

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

#[test]
fn lexer_test() {
    use chumsky::prelude::*;

    // Check if the lexer parses the example file without errors.
    let src = include_str!("../examples/last_will.simf");

    let (tokens, lex_errs) = lexer().parse(src).into_output_errors();
    let _ = tokens.unwrap();

    assert!(lex_errs.is_empty());
}
