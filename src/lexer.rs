use std::fmt;

use chumsky::prelude::{any, choice, end, just, recursive, skip_then_retry_until};
use chumsky::{error::Rich, extra, span::SimpleSpan, text, IterParser, Parser};

use crate::str::{Binary, Decimal, Hexadecimal};

pub type Spanned<T> = (T, SimpleSpan);
pub type Tokens<'src> = Vec<(Token<'src>, crate::error::Span)>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Token<'src> {
    // Keywords
    Fn,
    Let,
    Type,
    Mod,
    Const,
    Match,
    If,
    Else,

    // Control symbols
    /// `->`
    Arrow,
    /// `:`
    Colon,
    /// `;`
    Semi,
    /// `,`
    Comma,
    /// `=`
    Eq,
    /// `=>`
    FatArrow,
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `<`
    LAngle,
    /// `>`
    RAngle,

    // Number literals
    DecLiteral(Decimal),
    HexLiteral(Hexadecimal),
    BinLiteral(Binary),

    // Boolean literal
    Bool(bool),

    // Identifier
    Ident(&'src str),

    // Jets, witnesses, and params
    Jet(&'src str),
    Witness(&'src str),
    Param(&'src str),

    // Built-in functions
    Macro(&'src str),

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
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),

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
            Token::LAngle => write!(f, "<"),
            Token::RAngle => write!(f, ">"),

            Token::DecLiteral(s) => write!(f, "{}", s),
            Token::HexLiteral(s) => write!(f, "0x{}", s),
            Token::BinLiteral(s) => write!(f, "0b{}", s),

            Token::Ident(s) => write!(f, "{}", s),

            Token::Macro(s) => write!(f, "{}", s),

            Token::Jet(s) => write!(f, "jet::{}", s),
            Token::Witness(s) => write!(f, "witness::{}", s),
            Token::Param(s) => write!(f, "param::{}", s),

            Token::Bool(b) => write!(f, "{}", b),

            Token::Comment => write!(f, "comment"),
            Token::BlockComment => write!(f, "block_comment"),
        }
    }
}

pub fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, SimpleSpan>>>
{
    let digits_with_underscore = |radix: u32| {
        any()
            .filter(move |c: &char| c.is_digit(radix))
            .then(
                any()
                    .filter(move |c: &char| c.is_digit(radix) || *c == '_')
                    .repeated(),
            )
            .to_slice()
    };

    let num = digits_with_underscore(10)
        .map(|s: &str| Token::DecLiteral(Decimal::from_str_unchecked(s.replace('_', "").as_str())));
    let hex = just("0x")
        .ignore_then(digits_with_underscore(16))
        .map(|s: &str| {
            Token::HexLiteral(Hexadecimal::from_str_unchecked(s.replace('_', "").as_str()))
        });
    let bin = just("0b")
        .ignore_then(digits_with_underscore(2))
        .map(|s: &str| Token::BinLiteral(Binary::from_str_unchecked(s.replace('_', "").as_str())));

    let macros =
        choice((just("assert!"), just("panic!"), just("dbg!"), just("list!"))).map(Token::Macro);

    let keyword = text::ident().map(|s| match s {
        "fn" => Token::Fn,
        "let" => Token::Let,
        "type" => Token::Type,
        "mod" => Token::Mod,
        "const" => Token::Const,
        "match" => Token::Match,
        "if" => Token::If,
        "else" => Token::Else,
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        _ => Token::Ident(s),
    });

    let jet = just("jet::")
        .labelled("jet")
        .ignore_then(text::ident())
        .map(Token::Jet);
    let witness = just("witness::")
        .labelled("witness")
        .ignore_then(text::ident())
        .map(Token::Witness);
    let param = just("param::")
        .labelled("param")
        .ignore_then(text::ident())
        .map(Token::Param);

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
        just("<").to(Token::LAngle),
        just(">").to(Token::RAngle),
    ));

    let comment = just("//")
        .ignore_then(any().and_is(just('\n').not()).repeated())
        .to(Token::Comment);

    let block_comment = recursive(|block| {
        just("/*")
            .map_with(|_, e| e.span())
            .then(choice((block.ignored(), any().and_is(just("*/").not()).ignored())).repeated())
            .then(just("*/").or_not())
            .validate(|((open_span, _content), close), _span, emit| {
                if close.is_none() {
                    emit.emit(Rich::custom(open_span, "Unclosed block comment"));
                }
                Token::BlockComment
            })
    });
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

/// Lexes an input string into a stream of tokens with spans.
///
/// All comments in the input code are discarded.
pub fn lex<'src>(input: &'src str) -> (Option<Tokens<'src>>, Vec<crate::error::RichError>) {
    let (tokens, errors) = lexer().parse(input).into_output_errors();
    (
        tokens.map(|vec| {
            vec.into_iter()
                .map(|(tok, span)| (tok, crate::error::Span::from(span)))
                .filter(|(tok, _)| !matches!(tok, Token::Comment | Token::BlockComment))
                .collect::<Vec<_>>()
        }),
        errors
            .iter()
            .map(|err| {
                crate::error::RichError::new(
                    crate::error::Error::CannotParse(err.reason().to_string()),
                    (*err.span()).into(),
                )
            })
            .collect::<Vec<_>>(),
    )
}

#[cfg(test)]
mod tests {
    use chumsky::error::Rich;

    use super::*;

    fn lex<'src>(
        input: &'src str,
    ) -> (Option<Vec<Token<'src>>>, Vec<Rich<'src, char, SimpleSpan>>) {
        let (tokens, errors) = lexer().parse(input).into_output_errors();
        let tokens = tokens.map(|vec| vec.iter().map(|(tok, _)| tok.clone()).collect::<Vec<_>>());
        (tokens, errors)
    }

    /// Helper function to get the variant name of a token
    fn variant_name(token: &Token) -> &'static str {
        match token {
            Token::Fn => "Fn",
            Token::Let => "Let",
            Token::Type => "Type",
            Token::Mod => "Mod",
            Token::Const => "Const",
            Token::Match => "Match",
            Token::If => "If",
            Token::Else => "Else",
            Token::Arrow => "Arrow",
            Token::Colon => "Colon",
            Token::Semi => "Semi",
            Token::Comma => "Comma",
            Token::Eq => "Eq",
            Token::FatArrow => "FatArrow",
            Token::LParen => "LParen",
            Token::RParen => "RParen",
            Token::LBracket => "LBracket",
            Token::RBracket => "RBracket",
            Token::LBrace => "LBrace",
            Token::RBrace => "RBrace",
            Token::LAngle => "LAngle",
            Token::RAngle => "RAngle",
            Token::DecLiteral(_) => "DecLiteral",
            Token::HexLiteral(_) => "HexLiteral",
            Token::BinLiteral(_) => "BinLiteral",
            Token::Bool(_) => "Bool",
            Token::Ident(_) => "Ident",
            Token::Jet(_) => "Jet",
            Token::Witness(_) => "Witness",
            Token::Param(_) => "Param",
            Token::Macro(_) => "Macro",
            Token::Comment => "Comment",
            Token::BlockComment => "BlockComment",
        }
    }

    /// Macro to assert that a sequence of tokens matches the expected variant types
    macro_rules! assert_tokens_match {
        ($tokens:expr, $($expected:ident),* $(,)?) => {
            {
                let tokens = $tokens.as_ref().expect("Expected Some tokens");
                let expected_variants = vec![$( stringify!($expected) ),*];

                assert_eq!(
                    tokens.len(),
                    expected_variants.len(),
                    "Expected {} tokens, got {}.\nTokens: {:?}",
                    expected_variants.len(),
                    tokens.len(),
                    tokens
                );

                for (idx, (token, expected_variant)) in tokens.iter().zip(expected_variants.iter()).enumerate() {
                    let actual_variant = variant_name(token);
                    assert_eq!(
                        actual_variant,
                        *expected_variant,
                        "Token at index {} does not match: expected {}, got {} (token: {:?})",
                        idx,
                        expected_variant,
                        actual_variant,
                        token
                    );
                }
            }
        };
    }

    #[test]
    fn test_if_statement() {
        let input = "if true {0} else {1};";
        let (tokens, errors) = lex(input);
        assert!(errors.is_empty(), "Expected no errors, found: {:?}", errors);

        assert_tokens_match!(
            tokens, If, Bool, LBrace, DecLiteral, RBrace, Else, LBrace, DecLiteral, RBrace, Semi,
        );
    }

    #[test]
    fn test_block_comment_simple() {
        let input = "/* hello world */";
        let (tokens, errors) = lex(input);

        assert!(errors.is_empty(), "Expected no errors, found: {:?}", errors);
        assert_eq!(
            tokens,
            Some(vec![Token::BlockComment]),
            "Should produce a single block comment token"
        );
    }

    #[test]
    fn test_block_comment_nested() {
        let input = "/* outer /* inner */ outer */";
        let (tokens, errors) = lex(input);

        assert!(errors.is_empty());
        assert_eq!(tokens, Some(vec![Token::BlockComment]));
    }

    #[test]
    fn test_block_comment_deeply_nested() {
        let input = "/* 1 /* 2 /* 3 */ 2 */ 1 */";
        let (tokens, errors) = lex(input);

        assert!(errors.is_empty());
        assert_eq!(tokens, Some(vec![Token::BlockComment]));
    }

    #[test]
    fn test_block_comment_multiline() {
        let input = "/* \n line 1 \n /* inner \n line */ \n */";
        let (tokens, errors) = lex(input);

        assert!(errors.is_empty());
        assert_eq!(tokens, Some(vec![Token::BlockComment]));
    }

    #[test]
    fn test_block_comment_unclosed() {
        let input = "/* unclosed comment start";
        let (tokens, errors) = lex(input);

        assert_eq!(errors.len(), 1, "Expected exactly 1 error");

        let err = &errors[0];
        assert_eq!(err.span().start, 0);
        assert_eq!(err.span().end, 2);
        assert_eq!(err.to_string(), "Unclosed block comment");

        assert_eq!(tokens, Some(vec![Token::BlockComment]));
    }

    #[test]
    fn test_block_comment_partial_nesting_unclosed() {
        let input = "/* outer /* inner */";
        let (tokens, errors) = lex(input);

        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].span().start, 0);
        assert_eq!(tokens, Some(vec![Token::BlockComment]));
    }

    #[test]
    fn test_block_comment_double_unclosed() {
        let input = "/* outer /* inner";
        let (tokens, errors) = lex(input);

        assert_eq!(errors.len(), 2);

        assert_eq!(errors[0].span().start, 9);
        assert_eq!(errors[0].to_string(), "Unclosed block comment");

        assert_eq!(errors[1].span().start, 0);
        assert_eq!(errors[1].to_string(), "Unclosed block comment");

        assert_eq!(tokens, Some(vec![Token::BlockComment]));
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
}
