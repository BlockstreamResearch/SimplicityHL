use std::sync::Arc;

use either::Either;

use crate::error::Span;
use crate::pattern::Pattern;
use crate::str::{AliasName, Binary, Decimal, FunctionName, Hexadecimal, Identifier, ModuleName};
use crate::types::AliasedType;
use crate::TemplateProgramWitness;

use super::{
    Assignment, Call, CallName, ConstDecl, EnumDeclaration, EnumVariant, Expression,
    ExpressionInner, Function, FunctionParam, Item, Match, MatchArm, MatchPattern, Module, Program,
    SingleExpression, SingleExpressionInner, Statement, TypeAlias, UseDecl, UseItems, Visibility,
};

impl<'a> arbitrary::Arbitrary<'a> for UseDecl {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let visibility = Visibility::arbitrary(u)?;
        let path_len = u.int_in_range(2..=4)?;
        let path = (0..path_len)
            .map(|_| Identifier::arbitrary(u))
            .collect::<arbitrary::Result<_>>()?;
        let items = UseItems::arbitrary(u)?;

        Ok(Self {
            visibility,
            path,
            items,
            span: Span::DUMMY,
        })
    }
}

impl<'a> arbitrary::Arbitrary<'a> for EnumVariant {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let name = Identifier::arbitrary(u)?;
        let len = u.int_in_range(0..=3)?;
        let payload = (0..len)
            .map(|_| AliasedType::arbitrary(u))
            .collect::<arbitrary::Result<Arc<[AliasedType]>>>()?;
        Ok(Self {
            name,
            payload,
            span: Span::DUMMY,
        })
    }
}

impl<'a> arbitrary::Arbitrary<'a> for EnumDeclaration {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let visibility = Visibility::arbitrary(u)?;
        // `AliasName::arbitrary` already dodges every reserved alias name, so a generated declaration always re-parses
        let name = AliasName::arbitrary(u)?;
        let len = u.int_in_range(2..=8)?;
        let variants = (0..len)
            .map(|_| EnumVariant::arbitrary(u))
            .collect::<arbitrary::Result<Arc<[EnumVariant]>>>()?;
        Ok(Self {
            visibility,
            name,
            variants,
            span: Span::DUMMY,
        })
    }
}

fn generate_arbitrary_items<'a>(
    u: &mut arbitrary::Unstructured<'a>,
) -> arbitrary::Result<Vec<Item>> {
    let mut items_vec = Vec::new();

    let len = u.int_in_range(0..=2)?;
    for _ in 0..len {
        items_vec.push(<Item as arbitrary::Arbitrary>::arbitrary(u)?);
    }

    Ok(items_vec)
}

impl<'a> arbitrary::Arbitrary<'a> for Program {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut items_vec = generate_arbitrary_items(u)?;

        // Enum declarations are valid only at the top level of a file, so
        // they are generated here and not in `generate_arbitrary_items`,
        // which `Module::arbitrary` reuses for nested items: a nested enum
        // would display to source that no longer parses.
        //
        // TODO(enums): declarations alone leave construction, matching,
        // payload binding, and compilation unreached — the expression
        // generator does not produce `EnumConstruction`/`EnumMatch`
        // correlated with the declared enums. Generate a coherent
        // declaration plus an expression using one of its variants, and
        // consider a two-stage serde target (serialize -> deserialize as
        // `UnresolvedValues` -> resolve against the declared types) to
        // cover enum witness serialization.
        for _ in 0..u.int_in_range(0..=2u8)? {
            items_vec.push(Item::EnumDeclaration(EnumDeclaration::arbitrary(u)?));
        }

        // Three equally-likely modes for how `fn main()` is injected:
        //   0 — no explicit main (arbitrary items only)
        //   1 — main with arbitrary params and return type
        //   2 — main with no params and no return type (closest to valid)
        match u.int_in_range(0..=2u8)? {
            0 => {}
            1 => {
                let mut main_fn = <Function as crate::ArbitraryRec>::arbitrary_rec(u, 3)?;
                main_fn.name = FunctionName::main();
                items_vec.push(Item::Function(main_fn));
            }
            _ => {
                let mut main_fn = <Function as crate::ArbitraryRec>::arbitrary_rec(u, 3)?;
                main_fn.name = FunctionName::main();
                main_fn.params = Arc::from([]);
                main_fn.ret = None;
                items_vec.push(Item::Function(main_fn));
            }
        }

        let items: Arc<[Item]> = items_vec.into();
        Ok(Self {
            items,
            span: Span::DUMMY,
        })
    }
}

impl<'a> arbitrary::Arbitrary<'a> for Item {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        match u.int_in_range(0..=4)? {
            0 => Ok(Item::TypeAlias(TypeAlias::arbitrary(u)?)),
            1 => Ok(Item::Function(Function::arbitrary(u)?)),
            2 => Ok(Item::Use(UseDecl::arbitrary(u)?)),
            3 => Ok(Item::Module(Module::arbitrary(u)?)),
            4 => Ok(Item::Const(ConstDecl::arbitrary(u)?)),
            _ => unreachable!(),
        }
    }
}

impl<'a> arbitrary::Arbitrary<'a> for ConstDecl {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        use crate::ArbitraryRec;

        Ok(Self {
            visibility: Visibility::arbitrary(u)?,
            name: Identifier::arbitrary(u)?,
            ty: AliasedType::arbitrary(u)?,
            expr: Expression::arbitrary_rec(u, 3)?,
            span: Span::DUMMY,
        })
    }
}

impl<'a> arbitrary::Arbitrary<'a> for Function {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <Self as crate::ArbitraryRec>::arbitrary_rec(u, 3)
    }
}

impl crate::ArbitraryRec for Function {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let visibility = Visibility::arbitrary(u)?;
        let name = FunctionName::arbitrary(u)?;
        let len = u.int_in_range(0..=6)?;
        let params = (0..len)
            .map(|_| FunctionParam::arbitrary(u))
            .collect::<arbitrary::Result<Arc<[FunctionParam]>>>()?;
        let ret = Option::<AliasedType>::arbitrary(u)?;
        let body = Expression::arbitrary_rec(u, budget).map(Expression::into_block)?;
        Ok(Self {
            visibility,
            name,
            params,
            ret,
            body,
            span: Span::DUMMY,
        })
    }
}

impl<'a> arbitrary::Arbitrary<'a> for Module {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let visibility = Visibility::arbitrary(u)?;
        let name = ModuleName::arbitrary(u)?;
        let items_vec = generate_arbitrary_items(u)?;

        Ok(Self {
            visibility,
            name,
            items: items_vec.into(),
            span: Span::DUMMY,
        })
    }
}

impl crate::ArbitraryRec for Expression {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let inner = match budget.checked_sub(1) {
            None => SingleExpression::arbitrary_rec(u, budget).map(ExpressionInner::Single),
            Some(new_budget) => match bool::arbitrary(u)? {
                false => SingleExpression::arbitrary_rec(u, budget).map(ExpressionInner::Single),
                true => {
                    let len = u.int_in_range(0..=3)?;
                    let statements = (0..len)
                        .map(|_| Statement::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Statement]>>>()?;
                    let maybe_single = match bool::arbitrary(u)? {
                        false => None,
                        true => Expression::arbitrary_rec(u, new_budget)
                            .map(Arc::new)
                            .map(Some)?,
                    };
                    Ok(ExpressionInner::Block(statements, maybe_single))
                }
            },
        }?;
        Ok(Self {
            inner,
            span: Span::DUMMY,
        })
    }
}

impl crate::ArbitraryRec for Statement {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        match bool::arbitrary(u)? {
            false => Assignment::arbitrary_rec(u, budget).map(Self::Assignment),
            true => Expression::arbitrary_rec(u, budget).map(Self::Expression),
        }
    }
}

impl crate::ArbitraryRec for Assignment {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let pattern = Pattern::arbitrary(u)?;
        let ty = AliasedType::arbitrary(u)?;
        let expression = Expression::arbitrary_rec(u, budget)?;

        Ok(Self {
            pattern,
            ty,
            expression,
            span: Span::DUMMY,
        })
    }
}

impl crate::ArbitraryRec for SingleExpression {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;
        use SingleExpressionInner as S;

        let inner = match budget.checked_sub(1) {
            None => match u.int_in_range(0..=6)? {
                0 => bool::arbitrary(u).map(S::Boolean),
                1 => Binary::arbitrary(u).map(S::Binary),
                2 => Decimal::arbitrary(u).map(S::Decimal),
                3 => Hexadecimal::arbitrary(u).map(S::Hexadecimal),
                4 => Identifier::arbitrary(u).map(S::Variable),
                5 => TemplateProgramWitness::arbitrary(u).map(S::Witness),
                6 => Ok(S::Option(None)),
                _ => unreachable!(),
            },
            Some(new_budget) => match u.int_in_range(0..=15)? {
                0 => bool::arbitrary(u).map(S::Boolean),
                1 => Binary::arbitrary(u).map(S::Binary),
                2 => Decimal::arbitrary(u).map(S::Decimal),
                3 => Hexadecimal::arbitrary(u).map(S::Hexadecimal),
                4 => Identifier::arbitrary(u).map(S::Variable),
                5 => TemplateProgramWitness::arbitrary(u).map(S::Witness),
                6 => Ok(S::Option(None)),
                7 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(Some)
                    .map(S::Option),
                8 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(Either::Left)
                    .map(S::Either),
                9 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(Either::Right)
                    .map(S::Either),
                10 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(S::Expression),
                11 => Call::arbitrary_rec(u, new_budget).map(S::Call),
                12 => Match::arbitrary_rec(u, new_budget).map(S::Match),
                13 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Expression::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Expression]>>>()
                        .map(S::Tuple)
                }
                14 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Expression::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Expression]>>>()
                        .map(S::Array)
                }
                15 => {
                    let len = u.int_in_range(0..=3)?;
                    let elements = (0..len)
                        .map(|_| Expression::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Expression]>>>()?;
                    Ok(S::List(elements))
                }
                _ => unreachable!(),
            },
        }?;
        Ok(Self {
            inner,
            span: Span::DUMMY,
        })
    }
}

impl crate::ArbitraryRec for Call {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let name = CallName::arbitrary(u)?;
        let len = u.int_in_range(0..=3)?;
        let args = (0..len)
            .map(|_| Expression::arbitrary_rec(u, budget))
            .collect::<arbitrary::Result<Arc<[Expression]>>>()?;
        Ok(Self {
            name,
            args,
            span: Span::DUMMY,
        })
    }
}

impl crate::ArbitraryRec for Match {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let scrutinee = Expression::arbitrary_rec(u, budget).map(Arc::new)?;
        let (pat_l, pat_r) = match u.int_in_range(0..=2)? {
            0 => {
                let id_l = Pattern::arbitrary(u)?;
                let ty_l = AliasedType::arbitrary(u)?;
                let pat_l = MatchPattern::Left(id_l, ty_l);
                let id_r = Pattern::arbitrary(u)?;
                let ty_r = AliasedType::arbitrary(u)?;
                let pat_r = MatchPattern::Right(id_r, ty_r);
                (pat_l, pat_r)
            }
            1 => {
                let id_r = Pattern::arbitrary(u)?;
                let ty_r = AliasedType::arbitrary(u)?;
                let pat_r = MatchPattern::Some(id_r, ty_r);
                (MatchPattern::None, pat_r)
            }
            2 => (MatchPattern::False, MatchPattern::True),
            _ => unreachable!(),
        };
        let expr_l = Expression::arbitrary_rec(u, budget).map(Arc::new)?;
        let expr_r = Expression::arbitrary_rec(u, budget).map(Arc::new)?;
        Ok(Self {
            scrutinee,
            left: MatchArm {
                pattern: pat_l,
                expression: expr_l,
                span: Span::DUMMY,
            },
            right: MatchArm {
                pattern: pat_r,
                expression: expr_r,
                span: Span::DUMMY,
            },
            span: Span::DUMMY,
        })
    }
}
