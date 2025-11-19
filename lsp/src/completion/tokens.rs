use nom::{
    branch::alt,
    bytes::complete::{tag, take_while},
    character::complete::{multispace0, satisfy},
    combinator::{map, opt, recognize, value},
    multi::many0,
    sequence::{pair, preceded},
    IResult, Parser,
};

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Colon,
    DoubleColon,
    OpenAngle,
    CloseAngle,
    EqualSign,
    OpenBracket,
    ClosedBracket,
    Identifier(String),
    Jet,
}

fn parse_symbol(input: &str) -> IResult<&str, Token> {
    let mut parser = alt((
        value(Token::DoubleColon, tag("::")),
        value(Token::Colon, tag(":")),
        value(Token::OpenBracket, tag("(")),
        value(Token::ClosedBracket, tag(")")),
        value(Token::OpenAngle, tag("<")),
        value(Token::CloseAngle, tag(">")),
        value(Token::EqualSign, tag("=")),
    ));
    parser.parse(input)
}

fn parse_jet(input: &str) -> IResult<&str, Token> {
    let mut parser = value(
        Token::Jet,
        recognize(pair(
            tag("jet::"),
            opt(take_while(|c: char| c.is_alphanumeric() || c == '_')),
        )),
    );
    parser.parse(input)
}

fn parse_identifier(input: &str) -> IResult<&str, Token> {
    let mut parser = map(
        recognize(pair(
            satisfy(|c| c.is_alphabetic() || c == '_'),
            take_while(|c: char| c.is_alphanumeric() || c == '_'),
        )),
        |s: &str| Token::Identifier(s.to_string()),
    );
    parser.parse(input)
}

pub fn lex_tokens(input: &str) -> IResult<&str, Vec<Token>> {
    let mut parser = many0(preceded(
        multispace0,
        alt((parse_jet, parse_symbol, parse_identifier)),
    ));
    parser.parse(input)
}
