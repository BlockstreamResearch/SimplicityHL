# Unstable features

Unstable features are experimental compiler capabilities. They may change or be removed before
stabilization.

## User guide: Viewing available unstable features

You can list all currently available unstable features by running `simc --help`. The features are
displayed in the help output under the `-Z` flag section.

The output looks similar to this:

```text
  -Z, --unstable-feature <FEATURE>  Enable unstable features. Available features:
                                      imports   Import syntax: 'use', 'crate::', and import aliases
```

## User guide: Enabling unstable features

To enable an unstable feature, pass the `-Z <feature-name>` flag when compiling with `simc`.

## User guide: Current unstable features

|Feature|Description|
|---|---|
|imports|Enables import and module syntax, including `use`, `crate::`, and import aliases.|

## Developer guide: How unstable features are checked

Feature gating is a fail-closed validation step after parsing and before later compiler phases
consume the parsed program. Parsed syntax nodes declare the unstable features they require by
implementing `UnstableFeatureRequirements` and pushing `FeatureUse` values with precise spans.

For example, import syntax is represented by `UseDecl`, so `UseDecl` declares the `imports`
requirement:

```rust
impl UnstableFeatureRequirements for UseDecl {
    fn unstable_feature_uses(&self, out: &mut Vec<FeatureUse>) {
        out.push(FeatureUse::new(UnstableFeature::Imports, self.span));
    }
}
```

`UnstableFeatureManager` only checks whether declared requirements are enabled. It should not know
how to rediscover every syntax shape that can use a feature.

## Developer guide: Adding a new unstable feature

1. Add a variant to `UnstableFeature`.
2. Update `Display`, `FromStr`, `description`, and `all`.
3. Implement or update `UnstableFeatureRequirements` on the parsed syntax node that owns the new
   feature.
4. Add tests that compile successfully with the feature enabled and fail before resolution or
   compilation when the feature is disabled.

## Developer guide: Stabilizing an unstable feature

Remove the feature variant and the corresponding requirement declaration from the parsed syntax
node. Tests that are not explicitly about feature gating should keep using the normal helpers that
enable all unstable features by default.
