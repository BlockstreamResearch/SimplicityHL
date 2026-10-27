use crate::parse;
use crate::types::{ResolvedType, TypeDeconstructible};

use super::super::recovery::Failure;
use super::super::scope::Scope;
use super::super::{Assignment, Expression, Statement};
use super::AbstractSyntaxTree;

impl AbstractSyntaxTree for Statement {
    type From = parse::Statement;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        assert!(ty.is_unit(), "Statements cannot return anything");
        match from {
            parse::Statement::Assignment(assignment) => {
                Assignment::analyze(assignment, ty, scope).map(Self::Assignment)
            }
            parse::Statement::Expression(expression) => {
                Expression::analyze(expression, ty, scope).map(Self::Expression)
            }
        }
    }
}

impl AbstractSyntaxTree for Assignment {
    type From = parse::Assignment;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        assert!(ty.is_unit(), "Assignments cannot return anything");
        // The assignment is a statement that returns nothing.
        //
        // However, the expression evaluated in the assignment does have a type,
        // namely the type specified in the assignment.
        let ty_expr = scope.resolve_or_never(from.ty(), from);
        let expression = Expression::analyze(from.expression(), &ty_expr, scope);

        // The declared type tells what the pattern binds even if the expression failed,
        // so later statements see the same variables as on success.
        let pattern_matches = match from.pattern().is_of_type(&ty_expr) {
            Ok(typed_variables) => {
                for (identifier, ty) in typed_variables {
                    scope.bind_variable(identifier, ty, from);
                }
                true
            }
            Err(error) => {
                scope.report(error.with_span(*from.as_ref()));
                for identifier in from.pattern().identifiers() {
                    scope.bind_variable(identifier.clone(), ResolvedType::never(), from);
                }
                false
            }
        };

        match expression? {
            expression if pattern_matches => Ok(Self {
                pattern: from.pattern().clone(),
                expression,
                span: *from.as_ref(),
            }),
            _ => Err(Failure::Reported),
        }
    }
}
