use std::sync::Arc;

use crate::error::{Diagnostic, Error, Span, WithSpan};
use crate::parse;
use crate::pattern::Pattern;
use crate::str::AliasName;
use crate::types::{EnumInfo, EnumVariantInfo, ResolvedType};

use super::super::recovery::Failure;
use super::super::scope::Scope;
use super::super::{EnumConstruction, EnumMatch, EnumMatchArm, Expression, Match, MatchArm};
use super::AbstractSyntaxTree;

impl AbstractSyntaxTree for EnumConstruction {
    type From = parse::EnumConstruction;

    /// Analyze the construction of an enum variant, e.g. `Action::Refresh(sig, 3)`.
    ///
    /// Analysis is type-directed. The expected type must be an enum, and the written enum name must name it.
    /// In program source that means an alias in lexical scope, the same rule
    /// matches follow. In witness and argument files, which are parsed without
    /// a scope ([`Scope::unscoped_enum_names`]), the enum's declared name
    /// itself also matches.
    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        let span = *from.span();
        let Some(info) = ty.as_enum() else {
            return Err(Error::ExpressionUnexpectedType { ty: ty.clone() }).with_span(span)?;
        };

        // The written name must be the expected enum's.
        // Enums are declared at the top level, so only a single identifier can name one.
        // An alias in scope must resolve to the expected type.
        // Without a scope (witness and argument files) the declared name itself matches.
        let written = from.enum_path_string();
        let names_expected_enum = match from.enum_path() {
            [single] => {
                let alias = AliasName::from_ident(single);

                match scope.get_alias(&alias) {
                    // The written enum is broken, so its variants and payloads are unknown.
                    Ok(resolved) if resolved.is_never() => {
                        let _ = scope.analyze_all(from.args(), |arg, scope| {
                            Expression::analyze(arg, &resolved, scope)
                        });
                        return Err(Failure::Reported);
                    }
                    Ok(resolved) if resolved.compatible(ty) => true,
                    Ok(resolved) => Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: resolved,
                    })
                    .with_span(span)?,
                    Err(_) => scope.unscoped_enum_names() && written == info.name(),
                }
            }
            _ => false,
        };
        if !names_expected_enum {
            Err(Error::Grammar {
                msg: format!("`{written}` does not name enum `{}`", info.name()),
            })
            .with_span(span)?;
        }

        let (variant_index, variant) = info
            .variant(from.variant())
            .ok_or_else(|| enum_variant_error(from.variant().as_str(), info))
            .with_span(span)?;
        if from.args().len() != variant.payload().len() {
            Err(Error::Grammar {
                msg: format!(
                    "variant `{}` of enum `{}` carries {} payload value(s), found {}",
                    from.variant(),
                    info.name(),
                    variant.payload().len(),
                    from.args().len()
                ),
            })
            .with_span(span)?;
        }

        let payload = scope
            .analyze_all(
                from.args().iter().zip(variant.payload()),
                |(arg, payload_ty), scope| {
                    Expression::analyze(arg, payload_ty, scope).map(Arc::new)
                },
            )
            .map(Arc::from)?;

        Ok(EnumConstruction {
            variant_index,
            payload,
            span,
        })
    }
}

/// The given string does not name a variant of the enum.
fn enum_variant_error(found: &str, info: &EnumInfo) -> Error {
    let variants = info
        .variants()
        .iter()
        .map(|variant| variant.name().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    Error::Grammar {
        msg: format!(
            "`{found}` is not a variant of enum `{}`; expected one of: {variants}",
            info.name()
        ),
    }
}

impl AbstractSyntaxTree for EnumMatch {
    type From = parse::EnumMatch;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        let arms = from.arms();
        let span = *from.span();
        debug_assert!(!arms.is_empty(), "the parser rejects empty enum matches");

        let enum_name = arms[0].enum_path_string();
        let [single] = arms[0].enum_path() else {
            return Err(Error::Grammar {
                msg: format!(
                    "`{enum_name}` does not name an enum; enums are declared at the \
                     top level, so match arms name them by a single identifier"
                ),
            })
            .with_span(span)
            .map_err(Failure::from);
        };
        let alias = AliasName::from_ident(single);
        let enum_ty = scope.get_alias(&alias).with_span(span)?;
        let info = match enum_ty.as_enum() {
            Some(info) => info.clone(),
            None if enum_ty.is_never() => return Err(Failure::Reported),
            None => Err(Error::Grammar {
                msg: format!(
                    "`{enum_name}` is not an enum, so match arms of the form \
                         `{enum_name}::Variant` cannot apply to it"
                ),
            })
            .with_span(span)?,
        };

        // One slot per variant, in declaration order.
        // the order of the leaves of the enum's balanced sum.
        let mut arms_by_index: Vec<Option<&parse::EnumMatchArm>> =
            vec![None; info.variants().len()];

        scope.analyze_all(arms, |arm, _scope| {
            if arm.enum_path() != arms[0].enum_path() {
                Err(Error::Grammar {
                    msg: format!(
                        "all match arms must use the same enum; expected '{}', found '{}'",
                        enum_name,
                        arm.enum_path_string()
                    ),
                })
                .with_span(arm)?;
            }
            let (index, _) = info
                .variant(arm.variant())
                .ok_or_else(|| Error::Grammar {
                    msg: format!(
                        "variant '{}' is not defined in enum '{}'",
                        arm.variant(),
                        enum_name
                    ),
                })
                .with_span(arm)?;
            let slot = &mut arms_by_index[index];
            if slot.is_some() {
                Err(Error::Grammar {
                    msg: format!("duplicate arm for variant '{}'", arm.variant()),
                })
                .with_span(arm)?;
            }

            *slot = Some(arm);
            Ok(())
        })?;

        // One collect: Some(arms) iff every variant is covered.
        let covered: Option<Vec<&parse::EnumMatchArm>> = arms_by_index.iter().copied().collect();
        let Some(covered) = covered else {
            let missing: Vec<String> = arms_by_index
                .iter()
                .zip(info.variants())
                .filter(|(slot, _)| slot.is_none())
                .map(|(_, variant)| format!("'{}'", variant.name()))
                .collect();
            return Err(Error::Grammar {
                msg: format!(
                    "enum match on '{}' must cover all {} variants; missing: {}",
                    enum_name,
                    info.variants().len(),
                    missing.join(", ")
                ),
            })
            .with_span(span)
            .map_err(Failure::from);
        };

        // Analyze the scrutinee against the nominal enum type, so that
        // matching a value of a different enum (or any other type) against
        // this enum's variants is a type error.
        let scrutinee = Expression::analyze(from.scrutinee(), &enum_ty, scope).map(Arc::new)?;

        let arm_asts = scope
            .analyze_all(
                covered.into_iter().zip(info.variants()),
                |(arm, variant), scope| {
                    let arm_span = *arm.span();
                    let pattern = analyze_enum_arm_bindings(arm, variant, scope, arm_span)?;

                    scope.in_match_arm(|scope| {
                        let payload_ty = variant.payload_type();
                        let typed_variables = pattern.is_of_type(payload_ty).with_span(arm_span)?;
                        for (identifier, variable_ty) in typed_variables {
                            scope.bind_variable(identifier, variable_ty, arm_span);
                        }

                        let body =
                            Expression::analyze(arm.expression(), ty, scope).map(Arc::new)?;

                        Ok(EnumMatchArm {
                            pattern,
                            body,
                            span: arm_span,
                        })
                    })
                },
            )
            .map(Arc::from)?;

        Ok(Self {
            scrutinee,
            arms: arm_asts,
            span,
        })
    }
}

/// Check an enum match arm's payload bindings against the variant's declared
/// payload types and combine them into one pattern for the variant's leaf.
///
/// Unit variants bind nothing ([`Pattern::Ignore`]); a single binding stands
/// alone; multiple bindings form a tuple pattern, matching the tuple that a
/// multi-payload variant carries at its leaf.
fn analyze_enum_arm_bindings(
    arm: &parse::EnumMatchArm,
    variant: &EnumVariantInfo,
    scope: &Scope,
    span: Span,
) -> Result<Pattern, Diagnostic> {
    if arm.bindings().len() != variant.payload().len() {
        return Err(Error::Grammar {
            msg: format!(
                "variant '{}' of enum '{}' carries {} payload value(s), \
                 but the arm binds {}",
                arm.variant(),
                arm.enum_path_string(),
                variant.payload().len(),
                arm.bindings().len()
            ),
        })
        .with_span(span);
    }

    let mut patterns = Vec::with_capacity(arm.bindings().len());
    for ((pattern, declared), payload_ty) in arm.bindings().iter().zip(variant.payload()) {
        let declared = scope.resolve(declared).with_span(span)?;

        if !declared.compatible(payload_ty) {
            return Err(Error::ExpressionTypeMismatch {
                expected: payload_ty.clone(),
                found: declared,
            })
            .with_span(span);
        }

        patterns.push(pattern.clone());
    }

    let pattern = match patterns.len() {
        0 => Pattern::Ignore,
        1 => patterns[0].clone(),
        _ => Pattern::tuple(patterns),
    };
    Ok(pattern)
}

impl AbstractSyntaxTree for Match {
    type From = parse::Match;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        let scrutinee_ty = from.scrutinee_type();
        let scrutinee_ty = scope.resolve(&scrutinee_ty).with_span(from)?;
        let scrutinee =
            Expression::analyze(from.scrutinee(), &scrutinee_ty, scope).map(Arc::new)?;

        let analyze_arm = |arm: &parse::MatchArm, scope: &mut Scope| {
            scope.in_match_arm(|scope| {
                if let Some((pattern, arm_ty)) = arm.pattern().as_typed_pattern() {
                    let arm_ty = scope.resolve(arm_ty).with_span(arm)?;
                    let typed_variables = pattern.is_of_type(&arm_ty).with_span(arm)?;

                    for (identifier, ty) in typed_variables {
                        scope.bind_variable(identifier, ty, arm);
                    }
                }
                Expression::analyze(arm.expression(), ty, scope).map(Arc::new)
            })
        };

        // Each arm declares the types of its bindings, so the arms are independent:
        // analyze both and report the errors of each.
        let ast_l = analyze_arm(from.left(), scope).map_err(|failure| scope.report(failure));
        let ast_r = analyze_arm(from.right(), scope).map_err(|failure| scope.report(failure));
        let (Ok(ast_l), Ok(ast_r)) = (ast_l, ast_r) else {
            return Err(Failure::Reported)?;
        };

        Ok(Self {
            scrutinee,
            left: MatchArm {
                pattern: from.left().pattern().clone(),
                expression: ast_l,
                span: *from.left().span(),
            },
            right: MatchArm {
                pattern: from.right().pattern().clone(),
                expression: ast_r,
                span: *from.right().span(),
            },
            span: *from.as_ref(),
        })
    }
}
