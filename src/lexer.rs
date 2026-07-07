use std::fmt;

use chumsky::prelude::{any, choice, end, just, recursive, skip_then_retry_until};
use chumsky::{error::Rich, extra, span::SimpleSpan, text, IterParser, Parser};

use crate::driver::CRATE_STR;
use crate::error::{Error, RichError, Span};
use crate::str::{Binary, Decimal, Hexadecimal};
use crate::version::SIMC_STR;

pub type Spanned<T> = (T, SimpleSpan);
pub type Tokens<'src> = Vec<(Token<'src>, crate::error::Span)>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Token<'src> {
    // Keywords
    Pub,
    Use,
    As,
    Fn,
    Let,
    Type,
    Mod,
    Const,
    Match,
    Crate,
    /// Reserved for the compiler version directive, which the version prescan
    /// consumes before lexing; [`lex`] reports any occurrence as an error and drops
    /// the token.
    Simc,

    // Control symbols
    Arrow,
    /// Represents a contiguous `::` token.
    /// This prevents the lexer from allowing spaces between colons (e.g., `use a: :b`),
    DoubleColon,
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
    LAngle,
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
            Token::Pub => write!(f, "pub"),
            Token::Use => write!(f, "use"),
            Token::As => write!(f, "as"),
            Token::Fn => write!(f, "fn"),
            Token::Let => write!(f, "let"),
            Token::Type => write!(f, "type"),
            Token::Mod => write!(f, "mod"),
            Token::Const => write!(f, "const"),
            Token::Match => write!(f, "match"),
            Token::Crate => write!(f, "{}", CRATE_STR),
            Token::Simc => write!(f, "{}", SIMC_STR),

            Token::Arrow => write!(f, "->"),
            Token::DoubleColon => write!(f, "::"),
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

/// Recognizer for a `// ...` line comment.
fn line_comment<'src>(
) -> impl Parser<'src, &'src str, (), extra::Err<Rich<'src, char, SimpleSpan>>> + Clone {
    just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .ignored()
}

/// Recognizer for a (possibly nested) `/* ... */` block comment; an unterminated
/// comment is reported and swallows the rest of the input.
fn block_comment<'src>(
) -> impl Parser<'src, &'src str, (), extra::Err<Rich<'src, char, SimpleSpan>>> + Clone {
    recursive(|block| {
        just("/*")
            .map_with(|_, e| e.span())
            .then(choice((block, any().and_is(just("*/").not()).ignored())).repeated())
            .then(just("*/").or_not())
            .validate(|((open_span, ()), close), _span, emit| {
                if close.is_none() {
                    emit.emit(Rich::custom(open_span, "Unclosed block comment"));
                }
            })
    })
}

/// Trivia — whitespace and comments — shared with the version-directive scanner
/// (`version::SimcDirective::scan`) so the lexer and the scanner agree on comment
/// syntax.
pub(crate) fn trivia<'src>(
) -> impl Parser<'src, &'src str, (), extra::Err<Rich<'src, char, SimpleSpan>>> {
    choice((
        line_comment(),
        block_comment(),
        any().filter(|c: &char| c.is_whitespace()).ignored(),
    ))
    .repeated()
    .ignored()
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
        "pub" => Token::Pub,
        "use" => Token::Use,
        "as" => Token::As,
        "fn" => Token::Fn,
        "let" => Token::Let,
        "type" => Token::Type,
        "mod" => Token::Mod,
        "const" => Token::Const,
        "match" => Token::Match,
        CRATE_STR => Token::Crate,
        SIMC_STR => Token::Simc,
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        _ => Token::Ident(s),
    });

    let jet = just("jet")
        .ignore_then(just("::"))
        .ignore_then(text::ident())
        .map(Token::Jet);
    let witness = just("witness")
        .ignore_then(just("::"))
        .ignore_then(text::ident())
        .map(Token::Witness);
    let param = just("param")
        .ignore_then(just("::"))
        .ignore_then(text::ident())
        .map(Token::Param);

    let op = choice((
        just("->").to(Token::Arrow),
        just("=>").to(Token::FatArrow),
        just("=").to(Token::Eq),
        just("::").to(Token::DoubleColon),
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

    let comment = line_comment().to(Token::Comment);
    let block_comment = block_comment().to(Token::BlockComment);
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

/// Lexes an input string into a stream of tokens with spans, beginning at byte
/// offset `start` — the end of the version directive per `SimcDirective::prescan`,
/// or `0`. Spans are reported relative to the full input.
///
/// All comments in the input code are discarded.
pub fn lex(
    file_id: usize,
    input: &str,
    start: usize,
) -> (Option<Tokens<'_>>, Vec<crate::error::RichError>) {
    let (tokens, lex_errors) = lexer().parse(&input[start..]).into_output_errors();
    let shift = |span: SimpleSpan| Span::new(file_id, span.start + start..span.end + start);

    // The reserved-keyword errors come first: a stray directive also produces
    // follow-up errors for its `"<range>";` remnant, and the sentinel is their cause.
    let mut errors: Vec<RichError> = Vec::new();
    let tokens = tokens.map(|vec| {
        vec.into_iter()
            .filter_map(|(tok, span)| match tok {
                Token::Comment | Token::BlockComment => None,
                // The reserved keyword is a sentinel: the prescan consumed the one
                // legitimate directive before lexing, so any occurrence is misplaced.
                Token::Simc => {
                    errors.push(RichError::new(Error::ReservedSimcKeyword, shift(span)));
                    None
                }
                tok => Some((tok, shift(span))),
            })
            .collect()
    });

    errors.extend(lex_errors.into_iter().map(|err| {
        RichError::new(
            Error::CannotParse {
                msg: err.reason().to_string(),
            },
            shift(*err.span()),
        )
    }));

    (tokens, errors)
}

/// A list of all reserved keywords.
pub const KEYWORDS: &[&str] = &[
    "pub", "use", "as", "fn", "let", "type", "mod", "const", "match", CRATE_STR, SIMC_STR, "true",
    "false",
];

/// Checks whether a given string is a keyword.
pub fn is_keyword(s: &str) -> bool {
    KEYWORDS.contains(&s)
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
    fn simc_is_reserved() {
        // The prescan consumes the one legitimate leading directive before lexing,
        // so `lex` reports any `simc` it sees and drops the sentinel token.
        for src in ["simc", "fn simc() {}", "fn f() {}\nsimc"] {
            let (tokens, errors) = super::lex(0, src, 0);
            assert!(
                errors.iter().any(|e| e.to_string().contains("reserved")),
                "expected a reserved-keyword error for {src:?}, got: {errors:?}"
            );
            assert!(
                tokens
                    .expect("recovery keeps the stream")
                    .iter()
                    .all(|(tok, _)| !matches!(tok, Token::Simc)),
                "the sentinel must not reach the token stream for {src:?}"
            );
        }

        // Identifiers merely starting with `simc` are ordinary identifiers.
        let (tokens, errors) = lex("simcfoo");
        assert!(errors.is_empty(), "unexpected: {errors:?}");
        assert_eq!(tokens, Some(vec![Token::Ident("simcfoo")]));
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
