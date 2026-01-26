use std::collections::HashMap;
use std::fmt;

use crate::parse::ParseFromStr;
use crate::str::WitnessName;
use crate::types::ResolvedType;
use crate::value::Value;
use crate::witness::{Arguments, WitnessValues};
use crate::AbiMeta;
use serde::{de, ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};

struct WitnessMapVisitor;

impl<'de> de::Visitor<'de> for WitnessMapVisitor {
    type Value = HashMap<WitnessName, Value>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a map with string keys and value-map values")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: de::MapAccess<'de>,
    {
        let mut map = HashMap::new();
        while let Some((key, value)) = access.next_entry::<WitnessName, Value>()? {
            if map.insert(key.shallow_clone(), value).is_some() {
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
            .deserialize_map(WitnessMapVisitor)
            .map(Self::from)
    }
}

impl Serialize for AbiMeta {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ::serde::Serializer,
    {
        use ::serde::ser::SerializeStruct;
        use std::collections::HashMap;

        let mut state = serializer.serialize_struct("AbiMeta", 2)?;

        let witness_types_converted = self
            .witness_types
            .iter()
            .map(|(w_name, w_type)| (w_name.to_string(), w_type.to_string()))
            .collect::<HashMap<_, _>>();
        state.serialize_field("witness_types", &witness_types_converted)?;
        let witness_types_converted = self
            .param_types
            .iter()
            .map(|(w_name, w_type)| (w_name.to_string(), w_type.to_string()))
            .collect::<HashMap<_, _>>();
        state.serialize_field("parameter_types", &witness_types_converted)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for Arguments {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer
            .deserialize_map(WitnessMapVisitor)
            .map(Self::from)
    }
}

struct ValueMapVisitor;

impl<'de> de::Visitor<'de> for ValueMapVisitor {
    type Value = Value;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a map with \"value\" and \"type\" fields")
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
        deserializer.deserialize_map(ValueMapVisitor)
    }
}

struct ParserVisitor<A>(std::marker::PhantomData<A>);

impl<'de, A: ParseFromStr> de::Visitor<'de> for ParserVisitor<A> {
    type Value = A;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a valid string")
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        A::parse_from_str(value).map_err(E::custom)
    }
}

impl<'de> Deserialize<'de> for WitnessName {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(ParserVisitor::<Self>(std::marker::PhantomData))
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
            map.serialize_entry(name.as_inner(), &ValueMapSerializer(value))?;
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
}
