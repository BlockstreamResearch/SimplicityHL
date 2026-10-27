use std::sync::Arc;

use either::Either;

use crate::error::{Diagnostic, Error, WithSpan};
use crate::parse;
use crate::types::{ResolvedType, TypeConstructible, TypeDeconstructible};
use crate::value::{UIntValue, Value};

use super::super::recovery::Failure;
use super::super::scope::Scope;
use super::super::{
    Call, EnumConstruction, EnumMatch, Expression, ExpressionInner, Match, SingleExpression,
    SingleExpressionInner, Statement,
};
use super::AbstractSyntaxTree;

impl Expression {
    /// Analyze an expression from the parse tree in a const context without predefined variables.
    ///
    /// Check if the expression is of the given type.
    ///
    /// ## Const evaluation
    ///
    /// The returned expression might not be evaluable at compile time.
    /// The details depend on the current state of the SimplicityHL compiler.
    pub fn analyze_const(from: &parse::Expression, ty: &ResolvedType) -> Result<Self, Diagnostic> {
        // Without this check, a `!` from the caller could make the `expect` below panic,
        // or make analysis drop errors and accept a wrong value.
        if !ty.has_structural_type() {
            return Err(
                Error::ExpressionUnexpectedType { ty: ty.clone() }.with_span(*from.as_ref())
            );
        }

        // Value files carry no scope, so enum constructions may name the
        // enum by its declared name here — and only here.
        let mut empty_scope = Scope::for_value_parsing();
        let expression = Self::analyze(from, ty, &mut empty_scope)
            .map_err(|failure| empty_scope.report(failure));

        // Value parsing has no diagnostic manager: return the first error analysis found.
        match empty_scope.into_diagnostics().into_iter().next() {
            Some(error) => Err(error),
            // This cannot panic: a failed analysis always leaves an error,
            // because types with `!` were rejected above.
            None => Ok(expression.expect("every failure is reported to the scope")),
        }
    }
}

impl AbstractSyntaxTree for Expression {
    type From = parse::Expression;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        match from.inner() {
            parse::ExpressionInner::Single(single) => {
                let ast_single = SingleExpression::analyze(single, ty, scope)?;
                Ok(Self {
                    ty: ty.clone(),
                    inner: ExpressionInner::Single(ast_single),
                    span: *from.as_ref(),
                })
            }
            parse::ExpressionInner::Block(statements, expression) => {
                let (ast_statements, ast_expression) =
                    scope.in_block(|scope| -> Result<_, Failure> {
                        let ast_statements = scope.analyze_all(statements.iter(), |s, scope| {
                            Statement::analyze(s, &ResolvedType::unit(), scope)
                        });
                        let ast_expression = match expression {
                            Some(expression) => Expression::analyze(expression, ty, scope)
                                .map(Arc::new)
                                .map(Some),
                            None if ty.compatible(&ResolvedType::unit()) => Ok(None),
                            None => Err(Error::ExpressionTypeMismatch {
                                expected: ty.clone(),
                                found: ResolvedType::unit(),
                            })
                            .with_span(from)
                            .map_err(Failure::from),
                        }?;
                        Ok((Arc::from(ast_statements?), ast_expression))
                    })?;

                Ok(Self {
                    ty: ty.clone(),
                    inner: ExpressionInner::Block(ast_statements, ast_expression),
                    span: *from.as_ref(),
                })
            }
        }
    }
}

/// The sub-expressions of an expression that builds a value, or `None` for any other expression.
fn value_parts(from: &parse::SingleExpression) -> Option<Vec<&parse::Expression>> {
    use parse::SingleExpressionInner as Inner;

    match from.inner() {
        Inner::Boolean(_) | Inner::Decimal(_) | Inner::Binary(_) | Inner::Hexadecimal(_) => {
            Some(Vec::new())
        }
        Inner::Tuple(elements) | Inner::Array(elements) | Inner::List(elements) => {
            Some(elements.iter().collect())
        }
        Inner::Either(Either::Left(inner) | Either::Right(inner)) => Some(vec![inner.as_ref()]),
        Inner::Option(inner) => Some(inner.iter().map(Arc::as_ref).collect()),
        Inner::EnumConstruction(construction) => Some(construction.args().iter().collect()),
        _ => None,
    }
}

impl AbstractSyntaxTree for SingleExpression {
    type From = parse::SingleExpression;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        if ty.is_never() {
            if let Some(parts) = value_parts(from) {
                // No value has type `!`, so the value cannot be built, but its parts
                // can still have errors of their own.
                let _ =
                    scope.analyze_all(parts, |part, scope| Expression::analyze(part, ty, scope));
                return Err(Failure::Reported);
            }
        }

        let inner = match from.inner() {
            parse::SingleExpressionInner::Boolean(bit) => {
                if !ty.is_boolean() {
                    Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: ResolvedType::boolean(),
                    })
                    .with_span(from)?;
                }
                SingleExpressionInner::Constant(Value::from(*bit))
            }
            parse::SingleExpressionInner::Decimal(decimal) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                UIntValue::parse_decimal(decimal, ty)
                    .with_span(from)
                    .map(Value::from)
                    .map(SingleExpressionInner::Constant)?
            }
            parse::SingleExpressionInner::Binary(bits) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                let value = UIntValue::parse_binary(bits, ty).with_span(from)?;
                SingleExpressionInner::Constant(Value::from(value))
            }
            parse::SingleExpressionInner::Hexadecimal(bytes) => {
                let value = Value::parse_hexadecimal(bytes, ty).with_span(from)?;
                SingleExpressionInner::Constant(value)
            }
            parse::SingleExpressionInner::Witness(name) => {
                scope
                    .insert_witness(name.clone(), ty.clone())
                    .with_span(from)?;
                SingleExpressionInner::Witness(name.clone())
            }
            parse::SingleExpressionInner::Parameter(name) => {
                scope
                    .insert_parameter(name.shallow_clone(), ty.clone())
                    .with_span(from)?;
                SingleExpressionInner::Parameter(name.shallow_clone())
            }
            parse::SingleExpressionInner::Variable(identifier) => {
                let (inner, found) = match scope.get_variable(identifier).cloned() {
                    Some(bound_ty) => {
                        scope.insert_variable(identifier.clone(), bound_ty.clone());
                        (
                            SingleExpressionInner::Variable(identifier.clone()),
                            bound_ty,
                        )
                    }
                    None => {
                        let value = scope
                            .get_constant(identifier)
                            .cloned()
                            .ok_or(Error::UndefinedVariable {
                                identifier: identifier.clone(),
                            })
                            .with_span(from)?;
                        let found = value.ty().clone();
                        (SingleExpressionInner::Constant(value), found)
                    }
                };

                if !ty.compatible(&found) {
                    Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found,
                    })
                    .with_span(from)?;
                }

                inner
            }
            parse::SingleExpressionInner::Expression(parse) => {
                Expression::analyze(parse, ty, scope)
                    .map(Arc::new)
                    .map(SingleExpressionInner::Expression)?
            }
            parse::SingleExpressionInner::Tuple(tuple) => {
                let types = ty
                    .as_tuple()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                if tuple.len() != types.len() {
                    return Err(Error::ExpressionUnexpectedType { ty: ty.clone() })
                        .with_span(from)?;
                }

                scope
                    .analyze_all(
                        tuple.iter().zip(types.iter()),
                        |(el_parse, el_ty), scope| Expression::analyze(el_parse, el_ty, scope),
                    )
                    .map(Arc::from)
                    .map(SingleExpressionInner::Tuple)?
            }
            parse::SingleExpressionInner::Array(array) => {
                let (el_ty, size) = ty
                    .as_array()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;

                // The element type is known even if the size is wrong,
                // so the elements are analyzed either way.
                if array.len() != size {
                    scope.report(
                        Error::ExpressionUnexpectedType { ty: ty.clone() }
                            .with_span(*from.as_ref()),
                    );
                }

                scope
                    .analyze_all(array.iter(), |el_parse, scope| {
                        Expression::analyze(el_parse, el_ty, scope)
                    })
                    .map(Arc::from)
                    .map(SingleExpressionInner::Array)?
            }
            parse::SingleExpressionInner::List(list) => {
                let (el_ty, bound) = ty
                    .as_list()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;

                if bound.get() <= list.len() {
                    scope.report(
                        Error::ExpressionUnexpectedType { ty: ty.clone() }
                            .with_span(*from.as_ref()),
                    );
                }

                scope
                    .analyze_all(list.iter(), |e, scope| Expression::analyze(e, el_ty, scope))
                    .map(Arc::from)
                    .map(SingleExpressionInner::List)?
            }
            parse::SingleExpressionInner::Either(either) => {
                let (ty_l, ty_r) = ty
                    .as_either()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                match either {
                    Either::Left(parse_l) => Expression::analyze(parse_l, ty_l, scope)
                        .map(Arc::new)
                        .map(Either::Left),
                    Either::Right(parse_r) => Expression::analyze(parse_r, ty_r, scope)
                        .map(Arc::new)
                        .map(Either::Right),
                }
                .map(SingleExpressionInner::Either)?
            }
            parse::SingleExpressionInner::Option(maybe_parse) => {
                let ty = ty
                    .as_option()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                match maybe_parse {
                    Some(parse) => {
                        Some(Expression::analyze(parse, ty, scope).map(Arc::new)).transpose()
                    }
                    None => Ok(None),
                }
                .map(SingleExpressionInner::Option)?
            }
            parse::SingleExpressionInner::Call(call) => {
                Call::analyze(call, ty, scope).map(SingleExpressionInner::Call)?
            }
            parse::SingleExpressionInner::Match(match_) => {
                Match::analyze(match_, ty, scope).map(SingleExpressionInner::Match)?
            }
            parse::SingleExpressionInner::EnumConstruction(construction) => {
                EnumConstruction::analyze(construction, ty, scope)
                    .map(SingleExpressionInner::EnumConstruction)?
            }
            parse::SingleExpressionInner::EnumMatch(enum_match) => {
                EnumMatch::analyze(enum_match, ty, scope).map(SingleExpressionInner::EnumMatch)?
            }
        };

        Ok(Self {
            inner,
            ty: ty.clone(),
            span: *from.as_ref(),
        })
    }
}
