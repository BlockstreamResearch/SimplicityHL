use std::collections::HashMap;

use crate::error::Error;
use crate::str::WitnessName;
use crate::value::Value;
use crate::witness::{Arguments, WitnessTypes, WitnessValues};

// ============================================================================
// DEPRECATED: Old serde-based deserialization (type field in JSON)
// ============================================================================
//
// Previous implementation required users to specify types in JSON:
// {
//     "VAR_NAME": {
//         "value": "Left(0x...)",
//         "type": "Either<Signature, Signature>"
//     }
// }
//
// Issues with old approach:
// 1. Type information is already known by the compiler from program analysis
// 2. Users must manually annotate types they may not fully understand
// 3. Redundant type information clutters the witness JSON format
// 4. Prone to user errors with complex type syntax (Either, Signature, etc.)
//
// OLD CODE REFERENCE:
// ---
// struct WitnessMapVisitor;
// impl<'de> de::Visitor<'de> for WitnessMapVisitor {
//     type Value = HashMap<WitnessName, Value>;
//     fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error> { ... }
// }
// impl<'de> Deserialize<'de> for WitnessValues { ... }
// impl<'de> Deserialize<'de> for Arguments { ... }
//
// struct ValueMapVisitor;
// impl<'de> de::Visitor<'de> for ValueMapVisitor {
//     type Value = Value;
//     fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error> {
//         let mut value = None;
//         let mut ty = None;
//         while let Some(key) = access.next_key::<&str>()? {
//             match key {
//                 "value" => { value = Some(...) }
//                 "type" => { ty = Some(...) }
//                 _ => return Err(de::Error::unknown_field(...))
//             }
//         }
//         let ty = ResolvedType::parse_from_str(ty.unwrap())?;
//         Value::parse_from_str(value.unwrap(), &ty)?
//     }
// }
// impl<'de> Deserialize<'de> for Value { ... }
// ---

// ============================================================================
// NEW: Context-aware deserialization (type information from compiler)
// ============================================================================
//
// Type information is provided by the compiler through WitnessTypes/Parameters.
// Users only specify values in simplified JSON format without type annotations:
// {
//     "VAR_NAME": "Left(0x...)",
//     "ANOTHER_VAR": "0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
// }
//
// The compiler automatically resolves types based on program analysis,
// eliminating the need for users to manually specify type information.

impl WitnessValues {
    /// Deserialize witness values from JSON with compiler-provided type context.
    ///
    /// This method simplifies the witness JSON format by eliminating redundant
    /// type field annotations. The compiler provides type information through 
    /// WitnessTypes, allowing users to specify only the values they need to provide.
    ///
    /// # Arguments
    ///
    /// * `json` - JSON string with witness values in simple string format
    /// * `witness_types` - Type information from the compiled program
    ///
    /// # Example JSON Format
    ///
    /// ```json
    /// {
    ///     "WITNESS_VAR": "0x1234",
    ///     "SIGNATURE": "Left(0x...)",
    ///     "AMOUNT": "42"
    /// }
    /// ```
    ///
    /// Types are resolved from the compiled program, not from user input.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - JSON parsing fails
    /// - A witness variable is not found in witness_types
    /// - Value parsing fails for the resolved type
    /// - A witness variable is assigned multiple times
    pub fn from_json_with_types(
        json: &str,
        witness_types: &WitnessTypes,
    ) -> Result<Self, Error> {
        let json_value: serde_json::Map<String, serde_json::Value> =
            serde_json::from_str(json)
                .map_err(|e| Error::InvalidJsonFormat(format!("Failed to parse JSON: {}", e)))?;

        let mut map = HashMap::new();

        for (name_str, value_json) in json_value.iter() {
            let name = WitnessName::from_str_unchecked(name_str);

            // Retrieve type from compiler-provided context (WitnessTypes)
            // This is the key difference: type comes from the compiler, not JSON
            let ty = witness_types
                .get(&name)
                .ok_or_else(|| Error::UndefinedWitness(name.clone()))?;

            // Extract value string from JSON (simple format, not {"value": ..., "type": ...})
            // Type annotation needed here for serde_json::Value
            let value_str: &str = match value_json.as_str() {
                Some(s) => s,
                None => {
                    return Err(Error::InvalidJsonFormat(format!(
                        "Witness `{}` must be a string value, got {}",
                        name,
                        match value_json {
                            serde_json::Value::Null => "null",
                            serde_json::Value::Bool(_) => "boolean",
                            serde_json::Value::Number(_) => "number",
                            serde_json::Value::String(_) => "string",
                            serde_json::Value::Array(_) => "array",
                            serde_json::Value::Object(_) => "object",
                        }
                    )))
                }
            };

            // Parse value using compiler-provided type
            // This ensures type safety without requiring user to annotate types
            let value = Value::parse_from_str(value_str, ty)?;

            // Check for duplicate assignments
            if map.insert(name.clone(), value).is_some() {
                return Err(Error::WitnessMultipleAssignments(name.clone()));
            }
        }

        Ok(Self::from(map))
    }
}

impl Arguments {
    /// Deserialize program arguments from JSON with compiler-provided type context.
    ///
    /// Similar to WitnessValues::from_json_with_types, but for function parameters.
    /// Types are resolved from the compiled program through Parameters, not from JSON.
    ///
    /// # Arguments
    ///
    /// * `json` - JSON string with argument values in simple string format
    /// * `parameters` - Parameter type information from the compiled program
    ///
    /// # Example JSON Format
    ///
    /// ```json
    /// {
    ///     "PARAM_A": "42",
    ///     "PARAM_B": "0xabcd"
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - JSON parsing fails
    /// - A parameter is not found in parameters
    /// - Value parsing fails for the resolved type
    /// - A parameter is assigned multiple times
    pub fn from_json_with_types(
        json: &str,
        parameters: &crate::witness::Parameters,
    ) -> Result<Self, Error> {
        let json_value: serde_json::Map<String, serde_json::Value> =
            serde_json::from_str(json)
                .map_err(|e| Error::InvalidJsonFormat(format!("Failed to parse JSON: {}", e)))?;

        let mut map = HashMap::new();

        for (name_str, value_json) in json_value.iter() {
            let name = WitnessName::from_str_unchecked(name_str);

            // Retrieve type from compiler-provided context (Parameters)
            let ty = parameters
                .get(&name)
                .ok_or_else(|| Error::UndefinedParameter(name.clone()))?;

            // Extract value string from JSON (simple format)
            // Type annotation needed here for serde_json::Value
            let value_str: &str = match value_json.as_str() {
                Some(s) => s,
                None => {
                    return Err(Error::InvalidJsonFormat(format!(
                        "Parameter `{}` must be a string value, got {}",
                        name,
                        match value_json {
                            serde_json::Value::Null => "null",
                            serde_json::Value::Bool(_) => "boolean",
                            serde_json::Value::Number(_) => "number",
                            serde_json::Value::String(_) => "string",
                            serde_json::Value::Array(_) => "array",
                            serde_json::Value::Object(_) => "object",
                        }
                    )))
                }
            };

            // Parse value using compiler-provided type
            let value = Value::parse_from_str(value_str, ty)?;

            // Check for duplicate assignments
            if map.insert(name.clone(), value).is_some() {
                return Err(Error::ArgumentMultipleAssignments(name.clone()));
            }
        }

        Ok(Self::from(map))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests for new context-aware deserialization should be added here
    // Example test case for simplified JSON format:
    //
    // #[test]
    // fn witness_from_json_with_types() {
    //     let json = r#"{ "A": "42", "B": "0x12345678" }"#;
    //     let witness_types = /* create WitnessTypes with A: u32, B: u32 */;
    //     let witness = WitnessValues::from_json_with_types(json, &witness_types).unwrap();
    //     assert_eq!(witness.get(&WitnessName::from_str_unchecked("A")).unwrap().ty(), u32_type);
    // }
}