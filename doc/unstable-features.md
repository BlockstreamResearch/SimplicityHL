# Unstable features

Unstable features are experimental additions to the compiler that are still under development and can be changed drastically. Features that need more real-world testing are also considered as unstable. Once their design is finalized and they are proven reliable based on user feedback, they will be stabilized.

## User Guide: Viewing available unstable features

You can list all currently available unstable features by running `simc --help`. The features are displayed in the help output under the `-Z` flag section.

The output looks similar to this:
```
  -Z, --unstable-feature <FEATURE>  Enable unstable features. Available features:
                                      use-keyword     The 'use' keyword for using dependencies
                                      crate-keyword   The 'crate' keyword for referencing the local project root
                                      as-keyword      The 'as' keyword for aliasing imports
```

## User guide: Enabling unstable features

To enable an unstable feature, you can pass the `-Z <feature-name>` flag when compiling with `simc`. The name of the feature must exactly match one of the names listed by `simc --help`.

## User guide: Current unstable features

|Feature|Description|
|---|---|
|use-keyword|This feature enables work with imports for simplicity. More detailed description [here](./architecture.md#dependency-managing)|
|crate-keyword|This feature enables work with local imports such as crates for simplicity. More detailed description [here](./architecture.md#crate-and-module-paths)|
|as-keyword|This feature enables aliasing for imports. More detailed description [here](./architecture.md#dependency-managing)|

## Developer guide: How to add new unstable feature

Current unstable feature implementation assumes that feature could be found for certain `Item` and it's childs in parsed AST.

To add new unstable feature in [src/unstable.rs](../src/unstable.rs):

1. Update the `UnstableFeature` enum with your feature:
```rust
pub enum UnstableFeature {
    /// The `use` keyword for including multiple source files.
    UseKeyword,
    /// The `crate` keyword for referencing the local project root.
    CrateKeyword,
    /// The `as` keyword for aliasing imports.
    AsKeyword,
}
```

2. Update the display and from string functions:
```rust
impl fmt::Display for UnstableFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UseKeyword => write!(f, "use-keyword"),
            Self::CrateKeyword => write!(f, "crate-keyword"),
            Self::AsKeyword => write!(f, "as-keyword"),
        }
    }
}

impl FromStr for UnstableFeature {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "use-keyword" => Ok(UnstableFeature::UseKeyword),
            "crate-keyword" => Ok(UnstableFeature::CrateKeyword),
            "as-keyword" => Ok(UnstableFeature::AsKeyword),
            _ => Err(format!("Unknown unstable feature: '{}'", s)),
        }
    }
}
```

3. Add the description for your feature which will be shown by call of `simc --help`:
```rust
    pub fn description(&self) -> &'static str {
        match self {
            Self::UseKeyword => "The 'use' keyword for using dependencies",
            Self::CrateKeyword => "The 'crate' keyword for referencing the local project root",
            Self::AsKeyword => "The 'as' keyword for aliasing imports",
        }
    }
```

4. Add your feature to the `all()` function. If you forget this step, your feature will not be checked.
```rust
    pub fn all() -> &'static [UnstableFeature] {
        &[Self::UseKeyword, Self::CrateKeyword, Self::AsKeyword]
    }
```

5. Create a detection function for your feature and update the `detect_feature_in_item` function. Recomended to use `detect_<feature_name_in_snake_case>()` for naming the detection function. The function should contain all the logic to determine where the feature applies, whether it depends on a specific AST context, etc.

```rust
    fn detect_feature_in_item(self, item: &Item) -> Vec<Span> {
        match self {
            Self::UseKeyword => Self::detect_use_keyword(item),
            Self::CrateKeyword => Self::detect_crate_keyword(item),
            Self::AsKeyword => Self::detect_as_keyword(item),
        }
    }

        fn detect_use_keyword(item: &Item) -> Vec<Span> {
        match item {
            Item::Use(use_decl) => vec![*use_decl.span()],
            _ => vec![],
        }
    }

    fn detect_crate_keyword(item: &Item) -> Vec<Span> {
        match item {
            Item::Use(use_decl) if use_decl
                .drp_name()
                .is_ok_and(|drp| drp == crate::driver::CRATE_STR) =>
            {
                vec![*use_decl.span()]
            }
            _ => vec![],
        }
    }

    fn detect_as_keyword(item: &Item) -> Vec<Span> {
        match item {
            Item::Use(use_decl) => {
                let has_alias = match use_decl.items() {
                    UseItems::Single((_, alias)) => alias.is_some(),
                    UseItems::List(items) => items.iter().any(|(_, alias)| alias.is_some()),
                };
                if has_alias {
                    vec![*use_decl.span()]
                } else {
                    vec![]
                }
            }
            _ => vec![],
        }
    }

```

6. Update the [documentation](#user-guide-current-unstable-features) for your feature.

## Developer guide: How to delete or stabilize an unstable feature

Deleting and stabilizing an unstable feature is the exact opposite to the adding one. The developer should remove all the [functional added](#developer-guide-how-to-add-new-unstable-feature) for this feature.