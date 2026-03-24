//! Unstable (experimental) compiler feature flags.
//!
//! These are analogous to `rustc`'s `-Z` flags and must be explicitly opted
//! into on the command line with `-Z <flag-name>`. Unstable features may
//! change or be removed without notice.

use std::cell::Cell;
use std::fmt;
use std::str::FromStr;

/// A single unstable compiler feature flag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnstableFlag {
    /// Enable infix arithmetic operators: `+`, `-`, `*`, `/`, `%`.
    ///
    /// These operators have side effects (overflow/underflow panics for `+`/`-`,
    /// division-by-zero panics for `/`/`%`) and so are opt-in.
    InfixArithmeticOperators,
    // ^^^ Add new flags here. Each flag needs:
    //   1. A variant in this enum
    //   2. A bit position in `bit()`
    //   3. A name string in `name()` / `from_str()`
    //   4. An entry in `ALL`
}

impl UnstableFlag {
    const fn bit(self) -> u64 {
        match self {
            Self::InfixArithmeticOperators => 1 << 0,
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            Self::InfixArithmeticOperators => "infix_arithmetic_operators",
        }
    }

    /// All known flags, used for error messages.
    pub const ALL: &'static [Self] = &[Self::InfixArithmeticOperators];
}

impl fmt::Display for UnstableFlag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl FromStr for UnstableFlag {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "infix_arithmetic_operators" => Ok(Self::InfixArithmeticOperators),
            _ => {
                let known = Self::ALL
                    .iter()
                    .map(|f| f.name())
                    .collect::<Vec<_>>()
                    .join(", ");
                Err(format!(
                    "unknown unstable flag `{s}`. Known flags: {known}"
                ))
            }
        }
    }
}

/// A set of enabled unstable compiler flags.
///
/// Stored as a bitmask; adding a new flag only requires extending
/// [`UnstableFlag`] — no changes to this type are needed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UnstableFlags(u64);

impl UnstableFlags {
    /// Returns an empty flag set (all features disabled).
    pub const fn new() -> Self {
        Self(0)
    }

    /// Enable `flag` in this set.
    pub fn enable(&mut self, flag: UnstableFlag) {
        self.0 |= flag.bit();
    }

    /// Returns `true` if `flag` is enabled.
    pub fn is_enabled(self, flag: UnstableFlag) -> bool {
        self.0 & flag.bit() != 0
    }
}

// ---------------------------------------------------------------------------
// Thread-local parse context
// ---------------------------------------------------------------------------

thread_local! {
    static ACTIVE: Cell<u64> = const { Cell::new(0) };
}

/// Returns `true` if `flag` is currently active in this thread's parse context.
///
/// This is intended to be called from inside parser combinators, where the
/// active flags are set by [`with_flags`].
pub fn is_enabled(flag: UnstableFlag) -> bool {
    ACTIVE.with(|cell| cell.get() & flag.bit() != 0)
}

/// Run `f` with `flags` active on the current thread.
///
/// The previous flag state is restored when `f` returns, making this safe to
/// nest.
pub fn with_flags<R>(flags: UnstableFlags, f: impl FnOnce() -> R) -> R {
    let prev = ACTIVE.with(|cell| {
        let old = cell.get();
        cell.set(flags.0);
        old
    });
    let result = f();
    ACTIVE.with(|cell| cell.set(prev));
    result
}
