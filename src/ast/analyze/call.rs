use std::sync::Arc;

use crate::compile::{RawHashJets, RawHashJetsError};
use crate::debug::TrackedCallName;
use crate::error::{Error, WithSpan};
use crate::jet::{source_type, target_type};
use crate::parse;
use crate::str::AliasName;
use crate::types::{
    AliasedType, ResolvedType, StructuralType, TypeConstructible, TypeDeconstructible, UIntType,
};

use super::super::recovery::Failure;
use super::super::scope::Scope;
use super::super::{Call, CallName, Expression, FunctionParam};
use super::AbstractSyntaxTree;

/// Do `a` and `b` carry the same enum at every corresponding position?
///
/// Casts prove structural equality, but enums are nominal: a cast may
/// freely reshape enum-free structure (`(u16, u16)` into `u32`), while
/// every enum must map to itself at its position — otherwise variants
/// would convert by ordinal position, silently bypassing declared
/// identity.
///
/// Conservative on shape changes: an enum aligned across a reshaped
/// subtree (such as an array-to-tuple conversion) is rejected even when
/// the enum itself is unchanged.
///
/// TODO(enums): this walk aligns high-level constructors, so casts that
/// reshape only the container around an enum are rejected even when the
/// enum keeps its structural position, e.g. `Option<E>` to
/// `Either<(), E>`. A provenance-aware comparison — structural skeletons
/// with nominal enum leaves — would accept those; keep `List` types
/// conservative either way, since their partition layout complicates
/// position alignment.
fn cast_preserves_enum_identity(source: &ResolvedType, target: &ResolvedType) -> bool {
    source.matches_with(target, |src, dst| match (src.as_enum(), dst.as_enum()) {
        (Some(src), Some(dst)) => src == dst,
        // Differently shaped subtrees may convert freely as long as no
        // enum is involved on either side.
        (None, None) => !src.contains_enum() && !dst.contains_enum(),
        _ => false,
    })
}

impl AbstractSyntaxTree for Call {
    type From = parse::Call;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        fn check_argument_types(
            parse_args: &[parse::Expression],
            expected_tys: &[ResolvedType],
        ) -> Result<(), Error> {
            if parse_args.len() == expected_tys.len() {
                Ok(())
            } else {
                Err(Error::InvalidNumberOfArguments {
                    expected: expected_tys.len(),
                    found: parse_args.len(),
                })
            }
        }

        fn check_output_type(
            observed_ty: &ResolvedType,
            expected_ty: &ResolvedType,
        ) -> Result<(), Error> {
            if observed_ty.compatible(expected_ty) {
                Ok(())
            } else {
                Err(Error::ExpressionTypeMismatch {
                    expected: expected_ty.clone(),
                    found: observed_ty.clone(),
                })
            }
        }

        fn analyze_arguments(
            parse_args: &[parse::Expression],
            args_tys: &[ResolvedType],
            scope: &mut Scope,
        ) -> Result<Arc<[Expression]>, Failure> {
            scope
                .analyze_all(
                    parse_args.iter().zip(args_tys.iter()),
                    |(arg_parse, arg_ty), scope| Expression::analyze(arg_parse, arg_ty, scope),
                )
                .map(Arc::from)
        }

        let name = CallName::analyze(from, scope)?;
        let args = match name.clone() {
            CallName::Jet(jet) => {
                let args_tys = source_type(&*jet)
                    .iter()
                    .map(AliasedType::resolve_builtin)
                    .collect::<Result<Vec<ResolvedType>, AliasName>>()
                    .map_err(|alias| Error::UndefinedAlias { name: alias })
                    .with_span(from)?;
                let out_ty = target_type(&*jet)
                    .resolve_builtin()
                    .map_err(|alias| Error::UndefinedAlias { name: alias })
                    .with_span(from)?;
                scope.report_err(check_output_type(&out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_tys).with_span(from)?;
                scope.track_call(from, TrackedCallName::Jet);

                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::UnwrapLeft(right_ty) => {
                let args_tys = [ResolvedType::either(ty.clone(), right_ty)];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let args = analyze_arguments(from.args(), &args_tys, scope)?;
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::UnwrapLeft(arg_ty));
                args
            }
            CallName::UnwrapRight(left_ty) => {
                let args_tys = [ResolvedType::either(left_ty, ty.clone())];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let args = analyze_arguments(from.args(), &args_tys, scope)?;
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::UnwrapRight(arg_ty));
                args
            }
            CallName::IsNone(some_ty) => {
                let args_tys = [ResolvedType::option(some_ty)];
                let out_ty = ResolvedType::boolean();
                scope.report_err(check_output_type(&out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_tys).with_span(from)?;
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Unwrap => {
                let args_tys = [ResolvedType::option(ty.clone())];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                scope.track_call(from, TrackedCallName::Unwrap);
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Assert => {
                let args_tys = [ResolvedType::boolean()];
                let out_ty = ResolvedType::unit();
                scope.report_err(check_output_type(&out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_tys).with_span(from)?;
                scope.track_call(from, TrackedCallName::Assert);

                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Panic => {
                let args_tys = [];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                // panic! allows every output type because it will never return anything
                scope.track_call(from, TrackedCallName::Panic);
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Debug => {
                let args_tys = [ty.clone()];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let args = analyze_arguments(from.args(), &args_tys, scope)?;
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::Debug(arg_ty));
                args
            }
            CallName::TypeCast(source) => {
                // Casts prove structural equality, but enums are nominal:
                // every enum must map to itself at its structural position
                // (see `cast_preserves_enum_identity`), else same-shaped
                // enums would convert variants by ordinal position.
                if !source.contains_never()
                    && !ty.contains_never()
                    && (!cast_preserves_enum_identity(&source, ty)
                        || (source.has_structural_type()
                            && ty.has_structural_type()
                            && StructuralType::from(&source) != StructuralType::from(ty)))
                {
                    scope.report(
                        Error::InvalidCast {
                            source: source.clone(),
                            target: ty.clone(),
                        }
                        .with_span(*from.as_ref()),
                    );
                }

                let args_tys = [source];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Custom(function) => {
                let args_ty = function
                    .params()
                    .iter()
                    .map(FunctionParam::ty)
                    .cloned()
                    .collect::<Vec<ResolvedType>>();
                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                analyze_arguments(from.args(), &args_ty, scope)?
            }
            CallName::Fold(function, bound) => {
                // A list fold has the signature:
                //   fold::<f, N>(list: List<E, N>, initial_accumulator: A) -> A
                // where
                //   fn f(element: E, accumulator: A) -> A
                let element_ty = function.params().first().expect("foldable function").ty();
                let list_ty = ResolvedType::list(element_ty.clone(), bound);
                let accumulator_ty = function
                    .params()
                    .get(1)
                    .expect("foldable function")
                    .ty()
                    .clone();
                let args_ty = [list_ty, accumulator_ty];

                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                analyze_arguments(from.args(), &args_ty, scope)?
            }
            CallName::ArrayFold(function, size) => {
                // An array fold has the signature:
                //   array_fold::<f, N>(array: [E; N], initial_accumulator: A) -> A
                // where
                //   fn f(element: E, accumulator: A) -> A
                let element_ty = function.params().first().expect("foldable function").ty();
                let array_ty = ResolvedType::array(element_ty.clone(), size.get());
                let accumulator_ty = function
                    .params()
                    .get(1)
                    .expect("foldable function")
                    .ty()
                    .clone();
                let args_ty = [array_ty, accumulator_ty];

                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                analyze_arguments(from.args(), &args_ty, scope)?
            }
            CallName::RawHash(tuple_ty, _) => {
                // A raw hash has the signature:
                //   raw_hash::<T>(tuple: T) -> u256
                // where
                //   T is a tuple of u8, u16, u32, u64, u128 or u256
                let out_ty = ResolvedType::u256();
                scope.report_err(check_output_type(&out_ty, ty).with_span(from));

                let args_tys = [tuple_ty];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::ForWhile(function, _bit_width) => {
                // A for-while loop has the signature:
                //   for_while::<f>(initial_accumulator: A, readonly_context: C) -> Either<B, A>
                // where
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                //   N is a power of two
                let accumulator_ty = function
                    .params()
                    .first()
                    .expect("loopable function")
                    .ty()
                    .clone();
                let context_ty = function
                    .params()
                    .get(1)
                    .expect("loopable function")
                    .ty()
                    .clone();
                let args_ty = [accumulator_ty, context_ty];

                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                analyze_arguments(from.args(), &args_ty, scope)?
            }
        };

        Ok(Self {
            name,
            args,
            span: *from.as_ref(),
        })
    }
}

impl CallName {
    // Take parse::Call, so we have access to the span for pretty errors
    fn analyze(from: &parse::Call, scope: &mut Scope) -> Result<Self, Failure> {
        let name = match from.name() {
            parse::CallName::Jet(name) => match scope.jet_hinter().parse_jet(name.as_inner()) {
                Some(jet) if !jet.is_disabled() => Ok(Self::Jet(jet)),
                _ => Err(Error::JetDoesNotExist { name: name.clone() }).with_span(from),
            },
            parse::CallName::UnwrapLeft(right_ty) => scope
                .resolve(right_ty)
                .map(Self::UnwrapLeft)
                .with_span(from),
            parse::CallName::UnwrapRight(left_ty) => scope
                .resolve(left_ty)
                .map(Self::UnwrapRight)
                .with_span(from),
            parse::CallName::IsNone(some_ty) => {
                scope.resolve(some_ty).map(Self::IsNone).with_span(from)
            }
            parse::CallName::Unwrap => Ok(Self::Unwrap),
            parse::CallName::RawHash(tuple_ty) => {
                let tuple_ty = scope.resolve(tuple_ty).with_span(from)?;

                // Every element must be an integer with a `sha_256_ctx_8_add_N` jet.
                let widths = tuple_ty
                    .as_tuple()
                    .and_then(|elements| {
                        elements
                            .iter()
                            .map(|element| element.as_integer())
                            .collect::<Option<Vec<UIntType>>>()
                    })
                    .ok_or(Error::RawHashUnsupportedType {
                        ty: tuple_ty.clone(),
                    })
                    .with_span(from)?;

                match RawHashJets::new(scope.jet_hinter(), widths) {
                    Ok(jets) => Ok(Self::RawHash(tuple_ty, jets)),
                    Err(RawHashJetsError::UnsupportedWidth(_)) => {
                        Err(Error::RawHashUnsupportedType { ty: tuple_ty }).with_span(from)
                    }
                    Err(RawHashJetsError::Unavailable) => {
                        Err(Error::RawHashJetsUnavailable).with_span(from)
                    }
                }
            }
            parse::CallName::Assert => Ok(Self::Assert),
            parse::CallName::Panic => Ok(Self::Panic),
            parse::CallName::Debug => Ok(Self::Debug),
            parse::CallName::TypeCast(target) => {
                scope.resolve(target).map(Self::TypeCast).with_span(from)
            }
            parse::CallName::Custom(name) => Ok(Self::Custom(scope.get_function(name, from)?)),
            parse::CallName::ArrayFold(name, size) => {
                let function = scope.get_function(name, from)?;
                // A function that is used in a array fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if function.params().len() != 2
                    || !function.params()[1].ty().compatible(function.ret())
                {
                    Err(Error::FunctionNotFoldable { name: name.clone() }).with_span(from)
                } else {
                    Ok(Self::ArrayFold(function, *size))
                }
            }
            parse::CallName::Fold(name, bound) => {
                let function = scope.get_function(name, from)?;
                // A function that is used in a list fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if function.params().len() != 2
                    || !function.params()[1].ty().compatible(function.ret())
                {
                    Err(Error::FunctionNotFoldable { name: name.clone() }).with_span(from)
                } else {
                    Ok(Self::Fold(function, *bound))
                }
            }
            parse::CallName::ForWhile(name) => {
                let function = scope.get_function(name, from)?;
                // A function that is used in a for-while loop has the signature:
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                // where
                //   N is a power of two
                if function.params().len() != 3 {
                    return Err(Error::FunctionNotLoopable { name: name.clone() })
                        .with_span(from)?;
                }
                let accumulator_ty = function.params().first().unwrap().ty();
                let returns_accumulator = function.ret().is_never()
                    || matches!(
                        function.ret().as_either(),
                        Some((_, out_r)) if out_r.compatible(accumulator_ty)
                    );
                if !returns_accumulator {
                    return Err(Error::FunctionNotLoopable { name: name.clone() })
                        .with_span(from)?;
                }

                // Disable loops for u32 or higher since no one will want to run
                // 2^32 = 4294967296 ≈ 4 billion iterations.
                // The resulting Simplicity program will not fit into a Bitcoin block.
                let counter_ty = function.params().get(2).unwrap().ty();
                match counter_ty.as_integer() {
                    Some(
                        int_ty @ (UIntType::U1
                        | UIntType::U2
                        | UIntType::U4
                        | UIntType::U8
                        | UIntType::U16),
                    ) => Ok(Self::ForWhile(function, int_ty.bit_width())),
                    // The loop needs the width of the counter, which is unknown.
                    None if counter_ty.is_never() => return Err(Failure::Reported),
                    _ => Err(Error::FunctionNotLoopable { name: name.clone() }).with_span(from),
                }
            }
        };
        name.map_err(Failure::from)
    }
}
