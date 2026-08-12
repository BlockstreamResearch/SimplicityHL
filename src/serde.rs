use core::hash::Hash;
use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;

use crate::parse::ParseFromStr as _;
use crate::str::{Identifier, WitnessName};
use crate::types::ResolvedType;
use crate::value::Value;
use crate::witness::{Arguments, UnresolvedValue, UnresolvedValues, WitnessValues};
use crate::{AbiMeta, Parameters, WitnessTypes};
use serde::{de, ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};

/// Visitor for a map from identifiers to values of type `V`, rejecting duplicate names.
struct NamedMapVisitor<K, V> {
    key_map_fn: fn(&Identifier) -> K,
    phantom: PhantomData<V>,
}

impl<K, V> NamedMapVisitor<K, V> {
    const fn new(key_map_fn: fn(&Identifier) -> K) -> Self {
        Self {
            key_map_fn,
            phantom: PhantomData,
        }
    }
}

impl<'de, K: Eq + Hash, V: Deserialize<'de>> de::Visitor<'de> for NamedMapVisitor<K, V> {
    type Value = HashMap<K, V>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a map with string keys")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: de::MapAccess<'de>,
    {
        let mut map = HashMap::new();
        while let Some((key, value)) = access.next_entry::<Identifier, V>()? {
            if map.insert((self.key_map_fn)(&key), value).is_some() {
                return Err(de::Error::custom(format!("Name `{key}` is assigned twice")));
            }
        }
        Ok(map)
    }
}

impl<'de> Deserialize<'de> for WitnessValues {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer
            .deserialize_map(NamedMapVisitor::new(WitnessName::from_ident))
            .map(Self::from)
    }
}

struct UnresolvedValueVisitor;

impl<'de> de::Visitor<'de> for UnresolvedValueVisitor {
    type Value = UnresolvedValue;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a value string or a map with \"value\" and \"type\" fields")
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(UnresolvedValue::Untyped(value.to_owned()))
    }

    fn visit_map<M>(self, access: M) -> Result<Self::Value, M::Error>
    where
        M: de::MapAccess<'de>,
    {
        ValueMapVisitor
            .visit_map(access)
            .map(UnresolvedValue::Typed)
    }
}

impl<'de> Deserialize<'de> for UnresolvedValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // deserialize_any tells a bare string and a { value, type } map apart.
        // This requires a self-describing format (JSON).
        deserializer.deserialize_any(UnresolvedValueVisitor)
    }
}

impl<'de> Deserialize<'de> for UnresolvedValues {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer
            .deserialize_map(NamedMapVisitor::new(WitnessName::from_ident))
            .map(Self::from_map)
    }
}

impl Serialize for ResolvedType {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Enum mentions serialize as the enum's declared name, which is opaque.
        // Variants and wire encoding live in the program's declarations.
        serializer.serialize_str(&self.to_string())
    }
}

impl Serialize for AbiMeta {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ::serde::Serializer,
    {
        use ::serde::ser::SerializeStruct;

        let mut state = serializer.serialize_struct("AbiMeta", 2)?;
        state.serialize_field("witness_types", &self.witness_types)?;
        state.serialize_field("parameter_types", &self.param_types)?;
        state.end()
    }
}

impl Serialize for Parameters {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let map_ref = self.as_ref();
        let mut map = serializer.serialize_map(Some(map_ref.len()))?;
        for (key, value) in map_ref {
            map.serialize_entry(key.as_str(), value)?;
        }
        map.end()
    }
}

impl Serialize for WitnessTypes {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let map_ref = self.as_ref();
        let mut map = serializer.serialize_map(Some(map_ref.len()))?;
        for (key, value) in map_ref {
            map.serialize_entry(key.as_str(), value)?;
        }
        map.end()
    }
}

impl<'de> Deserialize<'de> for Arguments {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer
            .deserialize_map(NamedMapVisitor::new(WitnessName::from_ident))
            .map(Self::from)
    }
}

struct ValueMapVisitor;

impl<'de> de::Visitor<'de> for ValueMapVisitor {
    type Value = Value;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a map with \"value\" and \"type\" fields")
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Err(de::Error::custom(format!(
            "cannot deserialize the bare value `{value}` without the program's declared types; \
             deserialize into `UnresolvedValues` and resolve it against the program"
        )))
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: de::MapAccess<'de>,
    {
        let mut value = None;
        let mut ty = None;

        while let Some(key) = access.next_key::<&str>()? {
            match key {
                "value" => {
                    if value.is_some() {
                        return Err(de::Error::duplicate_field("value"));
                    }
                    value = Some(access.next_value::<&str>()?);
                }
                "type" => {
                    if ty.is_some() {
                        return Err(de::Error::duplicate_field("type"));
                    }
                    ty = Some(access.next_value::<&str>()?);
                }
                _ => {
                    return Err(de::Error::unknown_field(key, &["value", "type"]));
                }
            }
        }

        let ty = match ty {
            Some(s) => ResolvedType::parse_from_str(s).map_err(de::Error::custom)?,
            None => return Err(de::Error::missing_field("type")),
        };
        match value {
            Some(s) => Value::parse_from_str(s, &ty).map_err(de::Error::custom),
            None => Err(de::Error::missing_field("value")),
        }
    }
}

impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // deserialize_any lets a bare string (the form enum values serialize as) reach visit_str's directed error.
        // Self-describing formats only, as in `UnresolvedValue::deserialize`.
        deserializer.deserialize_any(ValueMapVisitor)
    }
}

impl<'de> Deserialize<'de> for Identifier {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ParserVisitor;
        impl<'de> de::Visitor<'de> for ParserVisitor {
            type Value = Identifier;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a valid string")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                crate::parse::ParseFromStr::parse_from_str(value).map_err(E::custom)
            }
        }

        deserializer.deserialize_str(ParserVisitor)
    }
}

struct WitnessMapSerializer<'a>(&'a HashMap<WitnessName, Value>);

impl<'a> Serialize for WitnessMapSerializer<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.0.len()))?;
        for (name, value) in self.0 {
            // Enum values serialize as their bare value string.
            // The { value, type } form cannot express them, since its type
            // string is parsed without the program's declarations.
            // Such values round-trip through `UnresolvedValues`, not through `Deserialize<WitnessValues>`.
            //
            // TODO: Consider serializing every value as a bare string and retiring the { value, type } form.
            // That drops "witness file readable without the program" entirely.
            if value.ty().contains_enum() {
                map.serialize_entry(name.as_str(), &value.to_string())?;
                continue;
            }
            map.serialize_entry(name.as_str(), &ValueMapSerializer(value))?;
        }
        map.end()
    }
}

struct ValueMapSerializer<'a>(&'a Value);

impl<'a> Serialize for ValueMapSerializer<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(2))?;
        map.serialize_entry("value", &self.0.to_string())?;
        map.serialize_entry("type", &self.0.ty().to_string())?;
        map.end()
    }
}

impl Serialize for WitnessValues {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        WitnessMapSerializer(self.as_inner()).serialize(serializer)
    }
}

impl Serialize for Arguments {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        WitnessMapSerializer(self.as_inner()).serialize(serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn witness_serde_duplicate_assignment() {
        let s = r#"{
  "A": { "value": "42", "type": "u32" },
  "A": { "value": "43", "type": "u16" }
}"#;

        match serde_json::from_str::<WitnessValues>(s) {
            Ok(_) => panic!("Duplicate witness assignment was falsely accepted"),
            Err(error) => assert!(error.to_string().contains("Name `A` is assigned twice")),
        }
    }

    fn unit_enum(name: &str, variants: &[&str]) -> ResolvedType {
        use crate::str::Identifier;
        use crate::types::{EnumInfo, EnumVariantInfo};
        use std::sync::Arc;

        let variants: Arc<[EnumVariantInfo]> = variants
            .iter()
            .map(|name| EnumVariantInfo::new(Identifier::from_str_unchecked(name), Arc::from([])))
            .collect();
        ResolvedType::enumeration(EnumInfo::new(Arc::from(name), variants))
    }

    #[test]
    fn abi_enum_type_serializes_as_name() {
        use crate::str::WitnessName;
        use crate::types::TypeConstructible;

        let action_ty = unit_enum("Action", &["Inherit", "ColdSpend"]);
        let witness_types = WitnessTypes::from(HashMap::from([
            (WitnessName::from_str_unchecked("ACTION"), action_ty.clone()),
            (
                WitnessName::from_str_unchecked("MAYBE"),
                ResolvedType::option(action_ty.clone()),
            ),
            (
                WitnessName::from_str_unchecked("PAIR"),
                ResolvedType::tuple([action_ty, unit_enum("Reaction", &["Fast", "Slow"])]),
            ),
            (
                WitnessName::from_str_unchecked("PLAIN"),
                crate::parse::ParseFromStr::parse_from_str("u32").unwrap(),
            ),
        ]));

        let json = serde_json::to_value(&witness_types).unwrap();
        assert_eq!(json["ACTION"], "Action");
        assert_eq!(json["MAYBE"], "Option<Action>");
        assert_eq!(json["PAIR"], "(Action, Reaction)");
        assert_eq!(json["PLAIN"], "u32");
    }

    #[test]
    fn enum_witness_value_serializes_as_variant_name() {
        use crate::str::{Identifier, WitnessName};

        let action_ty = unit_enum("Action", &["Inherit", "ColdSpend"]);
        let value = Value::enum_variant(
            &action_ty,
            &Identifier::from_str_unchecked("ColdSpend"),
            vec![],
        )
        .unwrap();
        let witness = WitnessValues::from(HashMap::from([(
            WitnessName::from_str_unchecked("ACTION"),
            value,
        )]));

        // Serializes in the bare form that UnresolvedValues can resolve back.
        let json = serde_json::to_value(&witness).unwrap();
        assert_eq!(json["ACTION"], "Action::ColdSpend");

        // The bare form round-trips through UnresolvedValues + resolve.
        let text = serde_json::to_string(&witness).unwrap();
        let unresolved: UnresolvedValues = serde_json::from_str(&text).unwrap();
        let witness_types = WitnessTypes::from(HashMap::from([(
            WitnessName::from_str_unchecked("ACTION"),
            action_ty,
        )]));
        let round_tripped: WitnessValues = unresolved.resolve(&witness_types).unwrap();
        assert_eq!(witness, round_tripped);

        // Deserializing it as WitnessValues directly cannot work without the
        // program's types; the error says where to go instead.
        let err = serde_json::from_str::<WitnessValues>(&text).unwrap_err();
        assert!(
            err.to_string().contains("UnresolvedValues"),
            "error should point at the resolution path: {err}"
        );
    }

    #[test]
    fn payload_enum_witness_value_round_trips() {
        use crate::str::{Identifier, WitnessName};
        use crate::types::{EnumInfo, EnumVariantInfo};
        use crate::value::ValueConstructible;
        use std::sync::Arc;

        let u32_ty = ResolvedType::parse_from_str("u32").unwrap();
        let variants: Arc<[EnumVariantInfo]> = Arc::from([
            EnumVariantInfo::new(Identifier::from_str_unchecked("Cold"), Arc::from([])),
            EnumVariantInfo::new(
                Identifier::from_str_unchecked("Refresh"),
                Arc::from([u32_ty.clone()]),
            ),
        ]);
        let action_ty = ResolvedType::enumeration(EnumInfo::new(Arc::from("Action"), variants));
        let value = Value::enum_variant(
            &action_ty,
            &Identifier::from_str_unchecked("Refresh"),
            vec![Value::u32(42)],
        )
        .unwrap();
        let witness = WitnessValues::from(HashMap::from([(
            WitnessName::from_str_unchecked("ACTION"),
            value,
        )]));

        // Payload variants serialize as their display form and round-trip through UnresolvedValues + resolve.
        let json = serde_json::to_value(&witness).unwrap();
        assert_eq!(json["ACTION"], "Action::Refresh(42)");

        let text = serde_json::to_string(&witness).unwrap();
        let unresolved: UnresolvedValues = serde_json::from_str(&text).unwrap();
        let witness_types = WitnessTypes::from(HashMap::from([(
            WitnessName::from_str_unchecked("ACTION"),
            action_ty,
        )]));
        let round_tripped: WitnessValues = unresolved.resolve(&witness_types).unwrap();
        assert_eq!(witness, round_tripped);
    }

    #[test]
    fn nested_enum_witness_value_serializes_as_bare_string() {
        use crate::str::{Identifier, WitnessName};
        use crate::types::TypeConstructible;
        use crate::value::ValueConstructible;

        let action_ty = unit_enum("Action", &["Hot", "Cold"]);
        let option_ty = ResolvedType::option(action_ty.clone());
        let cold = Value::enum_variant(&action_ty, &Identifier::from_str_unchecked("Cold"), vec![])
            .unwrap();
        let witness = WitnessValues::from(HashMap::from([(
            WitnessName::from_str_unchecked("MAYBE"),
            Value::some(cold),
        )]));

        // A nested enum value must not fall into the { value, type } form,
        // whose type string cannot be parsed without the program.
        let json = serde_json::to_value(&witness).unwrap();
        assert_eq!(json["MAYBE"], "Some(Action::Cold)");

        let text = serde_json::to_string(&witness).unwrap();
        let unresolved: UnresolvedValues = serde_json::from_str(&text).unwrap();
        let witness_types = WitnessTypes::from(HashMap::from([(
            WitnessName::from_str_unchecked("MAYBE"),
            option_ty,
        )]));
        let round_tripped: WitnessValues = unresolved.resolve(&witness_types).unwrap();
        assert_eq!(witness, round_tripped);
    }
}
