mod call;
mod expression;
mod matching;
mod program;
mod statement;

use crate::types::ResolvedType;

use super::recovery::Failure;
use super::scope::Scope;

/// Part of the abstract syntax tree that can be generated from a precursor in the parse tree.
trait AbstractSyntaxTree: Sized {
    /// Component of the parse tree.
    type From;

    /// Analyze a component from the parse tree
    /// and convert it into a component of the abstract syntax tree.
    ///
    /// Check if the analyzed expression is of the expected type.
    /// Statements return no values so their expected type is always unit.
    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure>;
}

#[cfg(test)]
mod span_tests {
    use crate::ast::{
        ElementsJetHinter, ExpressionInner, Function, Program, SingleExpressionInner,
    };
    use crate::error::DiagnosticManager;
    use crate::parse::{self, ParseFromStr};
    use crate::types::TypeConstructible;

    use super::*;

    #[test]
    fn analyzed_custom_function_preserves_declaration_and_parameter_spans() {
        let source = "fn helper(value: u8) -> u8 { value }";
        let parsed = parse::Function::parse_from_str(source).expect("function parses");
        let mut scope = Scope::new(Box::new(ElementsJetHinter));

        Function::analyze(&parsed, &ResolvedType::unit(), &mut scope).expect("function analyzes");
        let function = scope
            .get_function(parsed.name(), &parsed)
            .expect("function is registered in scope");

        assert_eq!(function.span().to_slice(source), Some(source));
        assert_eq!(
            function.params()[0].span().to_slice(source),
            Some("value: u8")
        );
    }

    #[test]
    fn analyzed_match_arms_preserve_their_parsed_spans() {
        let source = r#"fn main() {
    let input: Either<u8, u8> = Left(1);
    match input {
        Left(left: u8) => {},
        Right(right: u8) => {},
    }
}"#;
        let parsed = parse::Program::parse_from_str(source).expect("program parses");
        let program = Program::analyze(
            &parsed,
            Box::new(ElementsJetHinter),
            &mut DiagnosticManager::new(),
        )
        .expect("program analyzes");

        let ExpressionInner::Block(_, Some(last)) = program.main().inner() else {
            panic!("main body should end in a match");
        };
        let ExpressionInner::Single(single) = last.inner() else {
            panic!("match should be a single expression");
        };
        let SingleExpressionInner::Match(match_) = single.inner() else {
            panic!("expected a binary match");
        };

        assert_eq!(
            match_.left().span().to_slice(source),
            Some("Left(left: u8) => {},")
        );
        assert_eq!(
            match_.right().span().to_slice(source),
            Some("Right(right: u8) => {},")
        );
    }

    #[test]
    fn analyzed_enum_match_arms_preserve_their_parsed_spans() {
        let source = r#"enum Choice { First, Second, }
fn main() {
    let input: Choice = Choice::First;
    match input {
        Choice::First => {},
        Choice::Second => {},
    }
}"#;
        let parsed = parse::Program::parse_from_str(source).expect("program parses");
        let program = Program::analyze(
            &parsed,
            Box::new(ElementsJetHinter),
            &mut DiagnosticManager::new(),
        )
        .expect("program analyzes");

        let ExpressionInner::Block(_, Some(last)) = program.main().inner() else {
            panic!("main body should end in an enum match");
        };
        let ExpressionInner::Single(single) = last.inner() else {
            panic!("enum match should be a single expression");
        };
        let SingleExpressionInner::EnumMatch(match_) = single.inner() else {
            panic!("expected an enum match");
        };

        assert_eq!(
            match_.arms()[0].span().to_slice(source),
            Some("Choice::First => {},")
        );
        assert_eq!(
            match_.arms()[1].span().to_slice(source),
            Some("Choice::Second => {},")
        );
    }
}
