use std::fmt;

use either::Either;
use miniscript::iter::TreeLike;

use super::{
    Assignment, Call, CallName, ConstDecl, EnumDeclaration, EnumMatch, EnumMatchArm, ExprTree,
    Expression, Function, FunctionParam, Item, Match, MatchPattern, Module, Program,
    SingleExpression, SingleExpressionInner, Statement, TypeAlias, UseDecl, UseItems, Visibility,
};

impl fmt::Display for EnumDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}enum {} {{", self.visibility(), self.name())?;

        for variant in self.variants() {
            write!(f, " {}", variant.name())?;

            if let Some((first, rest)) = variant.payload().split_first() {
                write!(f, "({first}")?;

                for ty in rest {
                    write!(f, ", {ty}")?;
                }
                write!(f, ")")?;
            }
            write!(f, ",")?;
        }
        write!(f, " }}")
    }
}

/// Displays the arm's head (`Enum::Variant(bindings..)`), without the body.
impl fmt::Display for EnumMatchArm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{}", self.enum_path_string(), self.variant)?;

        if self.bindings.is_empty() {
            return Ok(());
        }

        f.write_str("(")?;
        for (i, (pattern, ty)) in self.bindings.iter().enumerate() {
            if 0 < i {
                f.write_str(", ")?;
            }
            write!(f, "{pattern}: {ty}")?;
        }
        f.write_str(")")
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for item in self.items() {
            writeln!(f, "{item}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TypeAlias(alias) => write!(f, "{alias}"),
            Self::Function(function) => write!(f, "{function}"),
            Self::Use(use_declaration) => write!(f, "{use_declaration}"),
            Self::EnumDeclaration(decl) => write!(f, "{decl}"),
            Self::Const(decl) => write!(f, "{decl}"),
            Self::Module(module) => write!(f, "{module}"),
            Self::Ignored => Ok(()),
        }
    }
}

impl fmt::Display for Visibility {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Public => write!(f, "pub "),
            Self::Private => write!(f, ""),
        }
    }
}

impl fmt::Display for TypeAlias {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}type {} = {};",
            self.visibility(),
            self.name(),
            self.ty()
        )
    }
}

impl fmt::Display for ConstDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}const {}: {} = {};",
            self.visibility(),
            self.name(),
            self.ty(),
            self.expr()
        )
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}fn {}(", self.visibility(), self.name())?;
        for (i, param) in self.params().iter().enumerate() {
            if 0 < i {
                write!(f, ", ")?;
            }
            write!(f, "{param}")?;
        }
        write!(f, ")")?;
        if let Some(ty) = self.ret() {
            write!(f, " -> {ty}")?;
        }
        write!(f, " {}", self.body())
    }
}

impl fmt::Display for FunctionParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.identifier(), self.ty())
    }
}

impl fmt::Display for UseDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let _ = write!(f, "{}use ", self.visibility());

        for (i, segment) in self.path.iter().enumerate() {
            if i > 0 {
                write!(f, "::")?;
            }
            write!(f, "{}", segment)?;
        }

        if !self.path.is_empty() {
            write!(f, "::")?;
        }

        write!(f, "{};", self.items)
    }
}

impl fmt::Display for UseItems {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UseItems::Single((ident, alias)) => {
                write!(f, "{}", ident)?;

                if let Some(alias) = alias {
                    write!(f, " as {}", alias)?;
                }

                Ok(())
            }
            UseItems::List(aliased_idents) => {
                let _ = write!(f, "{{");
                for (i, (ident, alias)) in aliased_idents.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ident)?;

                    if let Some(alias) = alias {
                        write!(f, " as {}", alias)?;
                    }
                }
                write!(f, "}}")
            }
        }
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}mod {} {{", self.visibility(), self.name())?;

        for item in self.items() {
            let item_str = item.to_string();

            for line in item_str.lines() {
                writeln!(f, "    {line}")?;
            }
        }

        write!(f, "}}")
    }
}

// TODO: Fix indentation and formatting logic. The current flat iterator approach cannot
// track AST depth, causing incorrect indentation for nested `Block` and `Match` nodes.
impl fmt::Display for ExprTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SingleExpressionInner as S;

        for data in self.verbose_pre_order_iter() {
            match &data.node {
                Self::Statement(..) if data.is_complete => writeln!(f, ";")?,
                Self::Expression(..) | Self::Statement(..) => {}
                Self::Block(..) => {
                    if data.n_children_yielded == 0 {
                        writeln!(f, "{{")?;
                    } else if !data.is_complete {
                        write!(f, "    ")?;
                    }
                    if data.is_complete {
                        writeln!(f, "}}")?;
                    }
                }
                Self::Assignment(assignment) => match data.n_children_yielded {
                    0 => write!(f, "let {}: {} = ", assignment.pattern(), assignment.ty())?,
                    n => debug_assert_eq!(n, 1),
                },
                Self::Single(single) => match single.inner() {
                    S::Boolean(bit) => write!(f, "{bit}")?,
                    S::Binary(binary) => write!(f, "0b{binary}")?,
                    S::Decimal(decimal) => write!(f, "{decimal}")?,
                    S::Hexadecimal(hexadecimal) => write!(f, "0x{hexadecimal}")?,
                    S::Variable(name) => write!(f, "{name}")?,
                    S::Witness(name) => write!(f, "witness::{name}")?,
                    S::Parameter(name) => write!(f, "param::{name}")?,
                    S::Option(None) => write!(f, "None")?,
                    S::Option(Some(_)) => match data.n_children_yielded {
                        0 => write!(f, "Some(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Either(Either::Left(_)) => match data.n_children_yielded {
                        0 => write!(f, "Left(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Either(Either::Right(_)) => match data.n_children_yielded {
                        0 => write!(f, "Right(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Expression(_) => match data.n_children_yielded {
                        0 => write!(f, "(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Call(..) | S::Match(..) | S::EnumMatch(..) | S::EnumConstruction(..) => {}
                    S::Tuple(tuple) => {
                        if data.n_children_yielded == 0 {
                            write!(f, "(")?;
                        } else if !data.is_complete || tuple.len() == 1 {
                            write!(f, ", ")?;
                        }
                        if data.is_complete {
                            write!(f, ")")?;
                        }
                    }
                    S::Array(..) => {
                        if data.n_children_yielded == 0 {
                            write!(f, "[")?;
                        } else if !data.is_complete {
                            write!(f, ", ")?;
                        }
                        if data.is_complete {
                            write!(f, "]")?;
                        }
                    }
                    S::List(..) => {
                        if data.n_children_yielded == 0 {
                            write!(f, "list![")?;
                        } else if !data.is_complete {
                            write!(f, ", ")?;
                        }
                        if data.is_complete {
                            write!(f, "]")?;
                        }
                    }
                },
                Self::Call(call) => {
                    if data.n_children_yielded == 0 {
                        write!(f, "{}(", call.name())?;
                    } else if !data.is_complete {
                        write!(f, ", ")?;
                    }
                    if data.is_complete {
                        write!(f, ")")?;
                    }
                }
                Self::EnumConstruction(construction) => {
                    match data.n_children_yielded {
                        0 => {
                            write!(
                                f,
                                "{}::{}",
                                construction.enum_path_string(),
                                construction.variant()
                            )?;
                            if !construction.args().is_empty() {
                                write!(f, "(")?;
                            }
                        }
                        _ if !data.is_complete => write!(f, ", ")?,
                        _ => {}
                    }
                    if data.is_complete && !construction.args().is_empty() {
                        write!(f, ")")?;
                    }
                }
                Self::Match(match_) => match data.n_children_yielded {
                    0 => write!(f, "match ")?,
                    1 => write!(f, "{{\n{} => ", match_.left().pattern())?,
                    2 => write!(f, ",\n{} => ", match_.right().pattern())?,
                    n => {
                        debug_assert_eq!(n, 3);
                        write!(f, ",\n}}")?;
                    }
                },
                Self::EnumMatch(enum_match) => match data.n_children_yielded {
                    0 => write!(f, "match ")?,
                    1 => write!(f, "{{\n{} => ", enum_match.arms()[0])?,
                    n if n <= enum_match.arms().len() => {
                        write!(f, ",\n{} => ", enum_match.arms()[n - 1])?;
                    }
                    _ => write!(f, ",\n}}")?,
                },
            }
        }

        Ok(())
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Expression(self))
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Statement(self))
    }
}

impl fmt::Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Assignment(self))
    }
}

impl fmt::Display for SingleExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Single(self))
    }
}

impl fmt::Display for Call {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Call(self))
    }
}

impl fmt::Display for CallName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CallName::Jet(jet) => write!(f, "jet::{jet}"),
            CallName::UnwrapLeft(ty) => write!(f, "unwrap_left::<{ty}>"),
            CallName::UnwrapRight(ty) => write!(f, "unwrap_right::<{ty}>"),
            CallName::Unwrap => write!(f, "unwrap"),
            CallName::IsNone(ty) => write!(f, "is_none::<{ty}>"),
            CallName::Assert => write!(f, "assert!"),
            CallName::Panic => write!(f, "panic!"),
            CallName::Debug => write!(f, "dbg!"),
            CallName::TypeCast(ty) => write!(f, "<{ty}>::into"),
            CallName::Custom(name) => write!(f, "{name}"),
            CallName::Fold(name, bound) => write!(f, "fold::<{name}, {bound}>"),
            CallName::ArrayFold(name, size) => write!(f, "array_fold::<{name}, {size}>"),
            CallName::ForWhile(name) => write!(f, "for_while::<{name}>"),
            CallName::RawHash(ty) => write!(f, "raw_hash::<{ty}>"),
        }
    }
}

impl fmt::Display for Match {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Match(self))
    }
}

impl fmt::Display for EnumMatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::EnumMatch(self))
    }
}

impl fmt::Display for MatchPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatchPattern::Left(i, ty) => write!(f, "Left({i}: {ty})"),
            MatchPattern::Right(i, ty) => write!(f, "Right({i}: {ty})"),
            MatchPattern::None => write!(f, "None"),
            MatchPattern::Some(i, ty) => write!(f, "Some({i}: {ty})"),
            MatchPattern::False => write!(f, "false"),
            MatchPattern::True => write!(f, "true"),
        }
    }
}
