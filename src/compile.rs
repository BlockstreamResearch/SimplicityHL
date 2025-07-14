//! Compile the parsed ast into a simplicity program

use std::sync::Arc;

use either::Either;
use simplicity::jet::Elements;
use simplicity::node::{CoreConstructible as _, JetConstructible as _};
use simplicity::{Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::ast::{
    Call, CallName, Expression, ExpressionInner, Match, Program, SingleExpression,
    SingleExpressionInner, Statement,
};
use crate::debug::CallTracker;
use crate::error::{Error, RichError, Span, WithSpan};
use crate::named::{CoreExt, PairBuilder};
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::pattern::{BasePattern, Pattern};
use crate::str::WitnessName;
use crate::types::{StructuralType, TypeDeconstructible};
use crate::value::StructuralValue;
use crate::witness::Arguments;
use crate::{ProgNode, Value};

/// Each SimplicityHL expression expects an _input value_.
/// A SimplicityHL expression is translated into a Simplicity expression
/// that similarly expects an _input value_.
///
/// SimplicityHL variable names are translated into Simplicity expressions
/// that extract the seeked value from the _input value_.
///
/// Each (nested) block expression introduces a new scope.
/// Bindings from inner scopes overwrite bindings from outer scopes.
/// Bindings live as long as their scope.
#[derive(Debug, Clone)]
struct Scope {
    /// For each scope, the set of assigned variables.
    ///
    /// A stack of scopes. Each scope is a stack of patterns.
    /// New patterns are pushed onto the top _(current, innermost)_ scope.
    ///
    /// ## Input pattern
    ///
    /// The stack of scopes corresponds to an _input pattern_.
    /// All valid input values match the input pattern.
    ///
    /// ## Example
    ///
    /// The stack `[[p1], [p2, p3]]` corresponds to a nested product pattern:
    ///
    /// ```text
    ///    .
    ///   / \
    /// p3   .
    ///     / \
    ///   p2   p1
    /// ```
    ///
    /// Inner scopes occur higher in the tree than outer scopes.
    /// Later assignments occur higher in the tree than earlier assignments.
    /// ```
    variables: Vec<Vec<Pattern>>,
    ctx: simplicity::types::Context,
    /// Tracker of function calls.
    call_tracker: Arc<CallTracker>,
    /// Values for parameters inside the SimplicityHL program.
    arguments: Arguments,
    include_debug_symbols: bool,
}

impl Scope {
    /// Create the main scope.
    ///
    /// _This function should be called at the start of the compilation and then never again._
    ///
    ///  ## Precondition
    ///
    /// The supplied `arguments` are consistent with the program's parameters.
    /// Call [`Arguments::is_consistent`] before calling this method!
    pub fn new(
        call_tracker: Arc<CallTracker>,
        arguments: Arguments,
        include_debug_symbols: bool,
    ) -> Self {
        Self {
            variables: vec![vec![Pattern::Ignore]],
            ctx: simplicity::types::Context::new(),
            call_tracker,
            arguments,
            include_debug_symbols,
        }
    }

    /// Create a child scope for a function that takes `input` of the given pattern.
    pub fn child(&self, input: Pattern) -> Self {
        Self {
            variables: vec![vec![input]],
            ctx: self.ctx.shallow_clone(),
            call_tracker: Arc::clone(&self.call_tracker),
            arguments: self.arguments.clone(),
            include_debug_symbols: self.include_debug_symbols,
        }
    }

    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(Vec::new());
    }

    /// Pop the current scope from the stack.
    ///
    /// # Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Empty stack");
    }

    /// Push an assignment to the current scope.
    ///
    /// Update the input pattern accordingly:
    ///
    /// ```text
    ///   .
    ///  / \
    /// p   previous
    /// ```
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert(&mut self, pattern: Pattern) {
        self.variables
            .last_mut()
            .expect("Empty stack")
            .push(pattern);
    }

    /// Get the input pattern.
    ///
    /// All valid input values match the input pattern.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    fn get_input_pattern(&self) -> Pattern {
        let mut it = self.variables.iter().flat_map(|scope| scope.iter());
        let first = it.next().expect("Empty stack");
        it.cloned()
            .fold(first.clone(), |acc, next| Pattern::product(next, acc))
    }

    /// Compute a Simplicity expression that takes a valid input value (that matches the input pattern)
    /// and that produces as output a value that matches the `target` pattern.
    ///
    /// ## Example
    ///
    /// ```
    /// let a: u8 = 0;
    /// let b = {
    ///     let b: u8 = 1;
    ///     let c: u8 = 2;
    ///     (a, b)  // here we seek the value of `(a, b)`
    /// };
    /// ```
    ///
    /// The input pattern looks like this:
    ///
    /// ```text
    ///   .
    ///  / \
    /// c   .
    ///    / \
    ///   b   .
    ///      / \
    ///     a   _
    /// ```
    ///
    /// The expression `drop (IOH & OH)` returns the seeked value.
    pub fn get(&self, target: &BasePattern) -> Option<PairBuilder<ProgNode>> {
        BasePattern::from(&self.get_input_pattern()).translate(&self.ctx, target)
    }

    /// Access the Simplicity type inference context.
    pub fn ctx(&self) -> &simplicity::types::Context {
        &self.ctx
    }

    /// Attach a debug symbol to the function body.
    /// This debug symbol can be used by the Simplicity runtime to print the call arguments
    /// during execution.
    ///
    /// The debug symbol is attached in such a way that a Simplicity runtime without support
    /// for debug symbols will simply ignore it. The semantics of the program remain unchanged.
    pub fn with_debug_symbol<S: AsRef<Span>>(
        &mut self,
        args: PairBuilder<ProgNode>,
        body: &ProgNode,
        span: &S,
    ) -> Result<PairBuilder<ProgNode>, RichError> {
        match self.call_tracker.get_cmr(span.as_ref()) {
            Some(cmr) if self.include_debug_symbols => {
                let false_and_args = ProgNode::bit(self.ctx(), false).pair(args);
                let nop_assert = ProgNode::assertl_drop(body, cmr);
                false_and_args.comp(&nop_assert).with_span(span)
            }
            _ => args.comp(body).with_span(span),
        }
    }

    pub fn get_argument(&self, name: &WitnessName) -> &Value {
        self.arguments
            .get(name)
            .expect("Precondition: Arguments are consistent with parameters")
    }
}

fn compile_blk(
    stmts: &[Statement],
    scope: &mut Scope,
    index: usize,
    last_expr: Option<&Expression>,
) -> Result<PairBuilder<ProgNode>, RichError> {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.compile(scope),
            None => Ok(PairBuilder::unit(scope.ctx())),
        };
    }
    match &stmts[index] {
        Statement::Assignment(assignment) => {
            let expr = assignment.expression().compile(scope)?;
            scope.insert(assignment.pattern().clone());
            let left = expr.pair(PairBuilder::iden(scope.ctx()));
            let right = compile_blk(stmts, scope, index + 1, last_expr)?;
            left.comp(&right).with_span(assignment)
        }
        Statement::Expression(expression) => {
            let left = expression.compile(scope)?;
            let right = compile_blk(stmts, scope, index + 1, last_expr)?;
            let pair = left.pair(right);
            let drop_iden = ProgNode::drop_(&ProgNode::iden(scope.ctx()));
            pair.comp(&drop_iden).with_span(expression)
        }
    }
}

impl Program {
    /// Compile the SimplicityHL source code to Simplicity target code.
    ///
    /// ## Precondition
    ///
    /// The supplied `arguments` are consistent with the program's parameters.
    /// Call [`Arguments::is_consistent`] before calling this method!
    pub fn compile(
        &self,
        arguments: Arguments,
        include_debug_symbols: bool,
    ) -> Result<ProgNode, RichError> {
        let mut scope = Scope::new(
            Arc::clone(self.call_tracker()),
            arguments,
            include_debug_symbols,
        );
        self.main().compile(&mut scope).map(PairBuilder::build)
    }
}

impl Expression {
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
        match self.inner() {
            ExpressionInner::Block(stmts, expr) => {
                scope.push_scope();
                let res = compile_blk(stmts, scope, 0, expr.as_ref().map(Arc::as_ref));
                scope.pop_scope();
                res
            }
            ExpressionInner::Single(e) => e.compile(scope),
        }
    }
}

impl SingleExpression {
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
        let expr = match self.inner() {
            SingleExpressionInner::Constant(value) => {
                let value = StructuralValue::from(value);
                PairBuilder::unit_scribe(scope.ctx(), value.as_ref())
            }
            SingleExpressionInner::Witness(name) => PairBuilder::witness(scope.ctx(), name.clone()),
            SingleExpressionInner::Parameter(name) => {
                let value = StructuralValue::from(scope.get_argument(name));
                PairBuilder::unit_scribe(scope.ctx(), value.as_ref())
            }
            SingleExpressionInner::Variable(identifier) => scope
                .get(&BasePattern::Identifier(identifier.clone()))
                .ok_or(Error::UndefinedVariable(identifier.clone()))
                .with_span(self)?,
            SingleExpressionInner::Expression(expr) => expr.compile(scope)?,
            SingleExpressionInner::Tuple(elements) | SingleExpressionInner::Array(elements) => {
                let compiled = elements
                    .iter()
                    .map(|e| e.compile(scope))
                    .collect::<Result<Vec<PairBuilder<ProgNode>>, RichError>>()?;
                let tree = BTreeSlice::from_slice(&compiled);
                tree.fold(PairBuilder::pair)
                    .unwrap_or_else(|| PairBuilder::unit(scope.ctx()))
            }
            SingleExpressionInner::List(elements) => {
                let compiled = elements
                    .iter()
                    .map(|e| e.compile(scope))
                    .collect::<Result<Vec<PairBuilder<ProgNode>>, RichError>>()?;
                let bound = self.ty().as_list().unwrap().1;
                let partition = Partition::from_slice(&compiled, bound);
                partition.fold(
                    |block, _size: usize| {
                        let tree = BTreeSlice::from_slice(block);
                        match tree.fold(PairBuilder::pair) {
                            None => PairBuilder::unit(scope.ctx()).injl(),
                            Some(pair) => pair.injr(),
                        }
                    },
                    PairBuilder::pair,
                )
            }
            SingleExpressionInner::Option(None) => PairBuilder::unit(scope.ctx()).injl(),
            SingleExpressionInner::Either(Either::Left(inner)) => {
                inner.compile(scope).map(PairBuilder::injl)?
            }
            SingleExpressionInner::Either(Either::Right(inner))
            | SingleExpressionInner::Option(Some(inner)) => {
                inner.compile(scope).map(PairBuilder::injr)?
            }
            SingleExpressionInner::Call(call) => call.compile(scope)?,
            SingleExpressionInner::Match(match_) => match_.compile(scope)?,
        };

        scope
            .ctx()
            .unify(
                &expr.as_ref().cached_data().arrow().target,
                &StructuralType::from(self.ty()).to_unfinalized(scope.ctx()),
                "",
            )
            .with_span(self)?;
        Ok(expr)
    }
}

impl Call {
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
        let args_ast = SingleExpression::tuple(self.args().clone(), *self.as_ref());
        let args = args_ast.compile(scope)?;

        match self.name() {
            CallName::Jet(name) => {
                let jet = ProgNode::jet(scope.ctx(), *name);
                scope.with_debug_symbol(args, &jet, self)
            }
            CallName::UnwrapLeft(..) => {
                let input_and_unit =
                    PairBuilder::iden(scope.ctx()).pair(PairBuilder::unit(scope.ctx()));
                let extract_inner = ProgNode::assertl_take(
                    &ProgNode::iden(scope.ctx()),
                    Cmr::fail(FailEntropy::ZERO),
                );
                let body = input_and_unit.comp(&extract_inner).with_span(self)?;
                scope.with_debug_symbol(args, body.as_ref(), self)
            }
            CallName::UnwrapRight(..) | CallName::Unwrap => {
                let input_and_unit =
                    PairBuilder::iden(scope.ctx()).pair(PairBuilder::unit(scope.ctx()));
                let extract_inner = ProgNode::assertr_take(
                    Cmr::fail(FailEntropy::ZERO),
                    &ProgNode::iden(scope.ctx()),
                );
                let body = input_and_unit.comp(&extract_inner).with_span(self)?;
                scope.with_debug_symbol(args, body.as_ref(), self)
            }
            CallName::IsNone(..) => {
                let input_and_unit =
                    PairBuilder::iden(scope.ctx()).pair(PairBuilder::unit(scope.ctx()));
                let is_right = ProgNode::case_true_false(scope.ctx());
                let body = input_and_unit.comp(&is_right).with_span(self)?;
                args.comp(&body).with_span(self)
            }
            CallName::Assert => {
                let jet = ProgNode::jet(scope.ctx(), Elements::Verify);
                scope.with_debug_symbol(args, &jet, self)
            }
            CallName::Panic => {
                // panic! ignores its arguments
                let fail = ProgNode::fail(scope.ctx(), FailEntropy::ZERO);
                scope.with_debug_symbol(args, &fail, self)
            }
            CallName::Debug => {
                // dbg! computes the identity function
                let iden = ProgNode::iden(scope.ctx());
                scope.with_debug_symbol(args, &iden, self)
            }
            CallName::TypeCast(..) => {
                // A cast converts between two structurally equal types.
                // Structural equality of SimplicityHL types A and B means
                // exact equality of the underlying Simplicity types of A and of B.
                // Therefore, a SimplicityHL cast is a NOP in Simplicity.
                Ok(args)
            }
            CallName::Custom(function) => {
                let mut function_scope = scope.child(function.params_pattern());
                let body = function.body().compile(&mut function_scope)?;
                args.comp(&body).with_span(self)
            }
            CallName::Fold(function, bound) => {
                let mut function_scope = scope.child(function.params_pattern());
                let body = function.body().compile(&mut function_scope)?;
                let fold_body = list_fold(*bound, body.as_ref()).with_span(self)?;
                args.comp(&fold_body).with_span(self)
            }
            CallName::ForWhile(function, bit_width) => {
                let mut function_scope = scope.child(function.params_pattern());
                let body = function.body().compile(&mut function_scope)?;
                let fold_body = for_while(*bit_width, body).with_span(self)?;
                args.comp(&fold_body).with_span(self)
            }
        }
    }
}

/// Fold a list of less than `2^n` elements using function `f`.
///
/// Function `f: E × A → A`
/// takes a list element of type `E` and an accumulator of type `A`,
/// and it produces an updated accumulator of type `A`.
///
/// The fold `(fold f)_n : E^(<2^n) × A → A`
/// takes the list of type `E^(<2^n)` and an initial accumulator of type `A`,
/// and it produces the final accumulator of type `A`.
fn list_fold(bound: NonZeroPow2Usize, f: &ProgNode) -> Result<ProgNode, simplicity::types::Error> {
    fn next_f_array(f_array: &ProgNode) -> Result<ProgNode, simplicity::types::Error> {
        /* f_(n + 1) :  E^(2^(n + 1)) × A → A
         * f_(n + 1) := OIH ▵ (OOH ▵ IH; f_n); f_n
         */
        let ctx = f_array.inference_context();
        let half1_acc = ProgNode::o().o().h(ctx).pair(ProgNode::i().h(ctx));
        let updated_acc = half1_acc.comp(f_array)?;
        let half2_acc = ProgNode::o().i().h(ctx).pair(updated_acc);
        half2_acc.comp(f_array).map(PairBuilder::build)
    }
    fn next_f_fold(
        f_array: &ProgNode,
        f_fold: &ProgNode,
    ) -> Result<ProgNode, simplicity::types::Error> {
        /* (fold f)_(n + 1) :  E<2^(n + 1) × A → A
         * (fold f)_(n + 1) := OOH ▵ (OIH ▵ IH);
         *                     case (drop (fold f)_n)
         *                          ((IOH ▵ (OH ▵ IIH; f_n)); (fold f)_n)
         */
        let ctx = f_array.inference_context();
        let case_input = ProgNode::o()
            .o()
            .h(ctx)
            .pair(ProgNode::o().i().h(ctx).pair(ProgNode::i().h(ctx)));
        let case_left = ProgNode::drop_(f_fold);

        let f_n_input = ProgNode::o().h(ctx).pair(ProgNode::i().i().h(ctx));
        let f_n_output = f_n_input.comp(f_array)?;
        let fold_n_input = ProgNode::i().o().h(ctx).pair(f_n_output);
        let case_right = fold_n_input.comp(f_fold)?;

        case_input
            .comp(&ProgNode::case(&case_left, case_right.as_ref())?)
            .map(PairBuilder::build)
    }

    /* f_0 :  E × A → A
     * f_0 := f
     */
    let mut f_array = f.clone();

    /* (fold f)_1 :  E^<2 × A → A
     * (fold f)_1 := case IH f_0
     */
    let ctx = f.inference_context();
    let ioh = ProgNode::i().h(ctx);
    let mut f_fold = ProgNode::case(ioh.as_ref(), &f_array)?;
    let mut i = NonZeroPow2Usize::TWO;

    while i < bound {
        f_array = next_f_array(&f_array)?;
        f_fold = next_f_fold(&f_array, &f_fold)?;
        i = i.mul2();
    }

    Ok(f_fold)
}

/// Run a function at most `2^(2^n)` times and return the first successful output.
///
/// Function `f: A × (C × 2^(2^(2^n))) → B + A`
/// takes an accumulator of type `A`, a readonly context of type `C`,
/// and a counter of type `2^(2^(2^n))` (unsigned integer of 2^n bits).
///
/// `f` may return a left `B` value, which is a successful output value.
/// In this case, the loop exists and returns this value.
///
/// Otherwise, the `f` returns a right `A` value, which is the updated accumulator.
/// In this case, the loop continues without returning anything.
/// The loop returns the final iterator after the final iteration
/// if `f` never returned a successful output.
fn for_while(
    bit_width: Pow2Usize,
    f: PairBuilder<ProgNode>,
) -> Result<PairBuilder<ProgNode>, simplicity::types::Error> {
    /* for_while_0 f :  E × A → A
     * for_while_0 f := (OH ▵ (IH ▵ false); f) ▵ IH;
     *                  case (injl OH)
     *                       (OH ▵ (IH ▵ true); f)
     */
    fn for_while_0(f: &ProgNode) -> Result<PairBuilder<ProgNode>, simplicity::types::Error> {
        let ctx = f.inference_context();
        let f_output = ProgNode::o()
            .h(ctx)
            .pair(ProgNode::i().h(ctx).pair(ProgNode::bit(ctx, false)))
            .comp(f)?;
        let case_input = f_output.pair(ProgNode::i().h(ctx));

        let x = ProgNode::injl(ProgNode::o().h(ctx).as_ref());
        let f_output = ProgNode::o()
            .h(ctx)
            .pair(ProgNode::i().h(ctx).pair(ProgNode::bit(ctx, true)))
            .comp(f)?;
        let case_output = ProgNode::case(&x, f_output.as_ref())?;

        case_input.comp(&case_output)
    }

    /* adapt f :  A × ((C × 2^(2^n)) × 2^(2^n)) → B + A
     * adapt f := OH ▵ (IOOH ▵ (IOIH ▵ IIH)); f
     * where
     *       f :  A × (C × 2^(2^(n + 1))) → B + A
     */
    fn adapt_f(f: &ProgNode) -> Result<PairBuilder<ProgNode>, simplicity::types::Error> {
        let ctx = f.inference_context();
        let f_input = ProgNode::o().h(ctx).pair(
            ProgNode::i()
                .o()
                .o()
                .h(ctx)
                .pair(ProgNode::i().o().i().h(ctx).pair(ProgNode::i().i().h(ctx))),
        );
        f_input.comp(f)
    }

    /* for_while_(n + 1) f :  E × A → A
     * for_while_(n + 1) f := for_while_n $ for_while_n $ adapt $ f
     *
     * If we write "0" for "for_while_0" and "1" for "adapt" and "." for function composition,
     * then the extended pattern looks like this:
     *
     * for_while_0 f := 0 . f
     * for_while_1 f := 0 . 0 . 1 . f
     * for_while_2 f := 0 . 0 . 1 . 0 . 0 . 1 . 1 . f
     * for_while_3 f := 0 . 0 . 1 . 0 . 0 . 1 . 1 . 0 . 0 . 1 . 0 . 0 . 1 . 1 . 1 . f
     *
     * The sequence of zeroes and ones starts with a single 0.
     * The next sequence is two copies of the previous sequence plus a final 1.
     *
     * The following Rust code implements this behavior:
     * First, a stack of zeroes is allocated. We know its final size, so we allocate exactly once.
     * The stack is repeatedly copied into itself to produce the seeked sequence of zeroes and ones.
     * Finally, "for_while_0" and "adapt" are applied to "f" by popping from the stack.
     */
    #[derive(Debug, Copy, Clone)]
    enum Task {
        /// "Zero"
        ForWhile0,
        /// "One"
        Adapt,
    }
    let max_stack = bit_width.mul2().get() - 1;
    let mut stack = vec![Task::ForWhile0; max_stack];

    let mut i = Pow2Usize::ONE.mul2();
    while i <= bit_width {
        let index = i.get() - 1;
        let (prefix, tail) = stack.as_mut_slice().split_at_mut(index);
        let suffix = &mut tail[..index];
        debug_assert_eq!(prefix.len(), suffix.len());
        suffix.copy_from_slice(prefix);
        tail[index] = Task::Adapt;
        i = i.mul2();
    }

    let mut for_while_f = f;

    while let Some(task) = stack.pop() {
        match task {
            Task::ForWhile0 => {
                for_while_f = for_while_0(for_while_f.as_ref())?;
            }
            Task::Adapt => {
                for_while_f = adapt_f(for_while_f.as_ref())?;
            }
        }
    }

    Ok(for_while_f)
}

impl Match {
    fn compile(&self, scope: &mut Scope) -> Result<PairBuilder<ProgNode>, RichError> {
        scope.push_scope();
        scope.insert(
            self.left()
                .pattern()
                .as_variable()
                .cloned()
                .map_or(Pattern::Ignore, Pattern::Identifier),
        );
        let left = self.left().expression().compile(scope)?;
        scope.pop_scope();

        scope.push_scope();
        scope.insert(
            self.right()
                .pattern()
                .as_variable()
                .cloned()
                .map_or(Pattern::Ignore, Pattern::Identifier),
        );
        let right = self.right().expression().compile(scope)?;
        scope.pop_scope();

        let scrutinee = self.scrutinee().compile(scope)?;
        let input = scrutinee.pair(PairBuilder::iden(scope.ctx()));
        let output = ProgNode::case(left.as_ref(), right.as_ref()).with_span(self)?;
        input.comp(&output).with_span(self)
    }
}
