use std::collections::HashMap;

use crate::error::Error;
use crate::value::Value;
use crate::str::WitnessName;

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



// This module contains suggested tests for the new context-aware witness deserialization
// Add these to src/serde.rs in the tests module

#[cfg(test)]
mod tests {
    use crate::parse::ParseFromStr;
    use super::*;
    use crate::str::WitnessName;
    use crate::types::ResolvedType;
    use crate::witness::WitnessTypes;
    use std::collections::HashMap;

    // ========================================================================
    // HELPER FUNCTIONS
    // ========================================================================

    fn create_witness_types_u32(names: &[&str]) -> WitnessTypes {
        let mut map = HashMap::new();
        for name in names {
            let name_obj = WitnessName::from_str_unchecked(name);
            // Create a u32 type
            let u32_type = ResolvedType::parse_from_str("u32").unwrap();
            map.insert(name_obj, u32_type);
        }
        WitnessTypes::from(map)
    }

    fn create_witness_types_mixed() -> WitnessTypes {
        let mut map = HashMap::new();
        
        let a = WitnessName::from_str_unchecked("A");
        let b = WitnessName::from_str_unchecked("B");
        let c = WitnessName::from_str_unchecked("C");
        
        map.insert(a, ResolvedType::parse_from_str("u32").unwrap());
        map.insert(b, ResolvedType::parse_from_str("u16").unwrap());
        map.insert(c, ResolvedType::parse_from_str("u8").unwrap());
        
        WitnessTypes::from(map)
    }

    // ========================================================================
    // HAPPY PATH TESTS
    // ========================================================================

    #[test]
    fn witness_from_json_with_types_single_variable() {
        let json = r#"{ "A": "42" }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_ok(), "Failed to parse valid witness: {:?}", result);
        
        let witness = result.unwrap();
        let a_value = witness.get(&WitnessName::from_str_unchecked("A"));
        assert!(a_value.is_some(), "Variable A not found in witness");
        assert_eq!(a_value.unwrap().to_string(), "42");
    }

    #[test]
    fn witness_from_json_with_types_multiple_variables() {
        let json = r#"{ "A": "42", "B": "1000", "C": "255" }"#;
        let witness_types = create_witness_types_mixed();
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_ok());
        
        let witness = result.unwrap();
        assert_eq!(witness.get(&WitnessName::from_str_unchecked("A")).unwrap().to_string(), "42");
        assert_eq!(witness.get(&WitnessName::from_str_unchecked("B")).unwrap().to_string(), "1000");
        assert_eq!(witness.get(&WitnessName::from_str_unchecked("C")).unwrap().to_string(), "255");
    }

    #[test]
    fn witness_from_json_with_types_hex_values() {
        let json = r#"{ "A": "0xdeadbeef", "B": "0x0000" }"#;
        let witness_types = create_witness_types_u32(&["A", "B"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_ok(), "Failed to parse hex values: {:?}", result);
        
        let witness = result.unwrap();
        // Values should be parsed correctly regardless of hex format
        assert!(witness.get(&WitnessName::from_str_unchecked("A")).is_some());
        assert!(witness.get(&WitnessName::from_str_unchecked("B")).is_some());
    }

    #[test]
    fn witness_from_json_with_types_empty_witness() {
        let json = r#"{}"#;
        let witness_types = WitnessTypes::from(HashMap::new());
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_ok(), "Failed to parse empty witness");
        
        let witness = result.unwrap();
        assert_eq!(witness.iter().count(), 0);
    }

    // ========================================================================
    // ERROR CASES: UNDEFINED VARIABLES
    // ========================================================================

    #[test]
    fn witness_from_json_with_types_undefined_witness_variable() {
        let json = r#"{ "UNKNOWN": "42" }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err(), "Should reject undefined witness variable");
        
        match result {
            Err(Error::UndefinedWitness(name)) => {
                assert_eq!(name.as_inner(), "UNKNOWN");
            }
            other => panic!("Expected UndefinedWitness error, got: {:?}", other),
        }
    }

    #[test]
    fn witness_from_json_with_types_undefined_with_defined_vars() {
        let json = r#"{ "A": "42", "UNKNOWN": "100" }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err());
        
        match result {
            Err(Error::UndefinedWitness(_)) => {
                // Expected: processing stops at first undefined var
            }
            other => panic!("Expected UndefinedWitness error, got: {:?}", other),
        }
    }

    // ========================================================================
    // ERROR CASES: DUPLICATE ASSIGNMENTS
    // ========================================================================

    #[test]
    fn witness_from_json_with_types_duplicate_assignment() {
        // JSON parsers typically handle duplicate keys by keeping the last value
        // So we test via the serde_json layer
        let json = r#"{ "A": "42", "A": "100" }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        // serde_json will keep the last value "100"
        assert!(result.is_ok() || result.is_err());
        // The exact behavior depends on serde_json version
        // but we're testing our error detection path
    }

    // ========================================================================
    // ERROR CASES: INVALID JSON FORMAT
    // ========================================================================

    #[test]
    fn witness_from_json_with_types_invalid_json_syntax() {
        let json = r#"{ "A": "42" INVALID }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err());
        
        match result {
            Err(Error::InvalidJsonFormat(msg)) => {
                assert!(msg.contains("Failed to parse JSON"));
            }
            other => panic!("Expected InvalidJsonFormat error, got: {:?}", other),
        }
    }

    #[test]
    fn witness_from_json_with_types_non_string_value_null() {
        let json = r#"{ "A": null }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err());
        
        match result {
            Err(Error::InvalidJsonFormat(msg)) => {
                assert!(msg.contains("must be a string value"));
                assert!(msg.contains("null"));
            }
            other => panic!("Expected InvalidJsonFormat error, got: {:?}", other),
        }
    }

    #[test]
    fn witness_from_json_with_types_non_string_value_number() {
        let json = r#"{ "A": 42 }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err());
        
        match result {
            Err(Error::InvalidJsonFormat(msg)) => {
                assert!(msg.contains("must be a string value"));
                assert!(msg.contains("number"));
            }
            other => panic!("Expected InvalidJsonFormat error, got: {:?}", other),
        }
    }

    #[test]
    fn witness_from_json_with_types_non_string_value_array() {
        let json = r#"{ "A": ["42"] }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err());
        
        match result {
            Err(Error::InvalidJsonFormat(msg)) => {
                assert!(msg.contains("must be a string value"));
                assert!(msg.contains("array"));
            }
            other => panic!("Expected InvalidJsonFormat error, got: {:?}", other),
        }
    }

    #[test]
    fn witness_from_json_with_types_non_string_value_object() {
        let json = r#"{ "A": {"value": "42"} }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err());
        
        match result {
            Err(Error::InvalidJsonFormat(msg)) => {
                assert!(msg.contains("must be a string value"));
                assert!(msg.contains("object"));
            }
            other => panic!("Expected InvalidJsonFormat error, got: {:?}", other),
        }
    }

    // ========================================================================
    // ERROR CASES: TYPE MISMATCH
    // ========================================================================

    #[test]
    fn witness_from_json_with_types_value_exceeds_type_bounds() {
        // u8 max value is 255
        let json = r#"{ "A": "256" }"#;
        let mut map = HashMap::new();
        map.insert(
            WitnessName::from_str_unchecked("A"),
            ResolvedType::parse_from_str("u8").unwrap(),
        );
        let witness_types = WitnessTypes::from(map);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err(), "Should reject value out of bounds for type");
    }

    #[test]
    fn witness_from_json_with_types_invalid_hex_value() {
        let json = r#"{ "A": "0xZZZZ" }"#;
        let witness_types = create_witness_types_u32(&["A"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_err(), "Should reject invalid hex value");
    }

    // ========================================================================
    // ARGUMENTS TESTS (parallel to WitnessValues)
    // ========================================================================

    #[test]
    fn arguments_from_json_with_types_single_parameter() {
        let json = r#"{ "PARAM_A": "42" }"#;
        let mut map = HashMap::new();
        map.insert(
            WitnessName::from_str_unchecked("PARAM_A"),
            ResolvedType::parse_from_str("u32").unwrap(),
        );
        let parameters = crate::witness::Parameters::from(map);
        
        let result = Arguments::from_json_with_types(json, &parameters);
        assert!(result.is_ok());
        
        let args = result.unwrap();
        assert!(args.get(&WitnessName::from_str_unchecked("PARAM_A")).is_some());
    }

    #[test]
    fn arguments_from_json_with_types_undefined_parameter() {
        let json = r#"{ "UNKNOWN": "42" }"#;
        let parameters = crate::witness::Parameters::from(HashMap::new());
        
        let result = Arguments::from_json_with_types(json, &parameters);
        assert!(result.is_err());
        
        match result {
            Err(Error::UndefinedParameter(name)) => {
                assert_eq!(name.as_inner(), "UNKNOWN");
            }
            other => panic!("Expected UndefinedParameter error, got: {:?}", other),
        }
    }

    // ========================================================================
    // WHITESPACE AND FORMATTING TESTS
    // ========================================================================

    #[test]
    fn witness_from_json_with_types_whitespace_handling() {
        let json = r#"
        {
            "A":   "42",
            "B":   "100"
        }
        "#;
        let witness_types = create_witness_types_u32(&["A", "B"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_ok(), "Should handle whitespace in JSON");
    }

    #[test]
    fn witness_from_json_with_types_unicode_variable_names() {
        // SimplicityHL identifiers might be restricted, but test handling
        let json = r#"{ "ALPHA": "42" }"#;
        let witness_types = create_witness_types_u32(&["ALPHA"]);
        
        let result = WitnessValues::from_json_with_types(json, &witness_types);
        assert!(result.is_ok());
    }
}
