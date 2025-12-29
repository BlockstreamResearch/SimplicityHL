use std::collections::HashMap;

use crate::error::Error;
use crate::str::WitnessName;
use crate::value::Value;
use crate::witness::{Arguments, WitnessTypes, WitnessValues};

// ============================================================================
// Context-aware deserialization with optional description field
// ============================================================================
//
// NEW FORMAT: Users can now add optional "description" fields
// {
//     "VAR_NAME": "Left(0x...)",
//     "description": "Optional comment about this witness file",
//     "ANOTHER_VAR": "0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
// }
//
// Special keys that are ignored:
// - "description" (top-level comment for the entire witness file)
// - Any key starting with "_" (conventionally used for comments)
// - "_<witness_name>" (can be used to provide hints about specific witnesses)
//
// Example with hints:
// {
//     "pubkey": "0x...",
//     "_pubkey": "Bitcoin public key for multisig",
//     "signature": "Left(0x...)",
//     "_signature": "ECDSA signature of the transaction",
//     "description": "Witness data for Bitcoin transaction #12345"
// }
//
// The compiler automatically ignores these comment fields.

impl WitnessValues {
    /// Deserialize witness values from JSON with compiler-provided type context.
    ///
    /// This method simplifies the witness JSON format by eliminating redundant
    /// type field annotations. The compiler provides type information through 
    /// WitnessTypes, allowing users to specify only the values they need to provide.
    ///
    /// Special features:
    /// - "description" field: Top-level comment for the witness file (ignored)
    /// - "_<name>" fields: Comments/hints for specific witnesses (ignored)
    /// - Any field starting with "_" is treated as a comment (ignored)
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
    ///     "pubkey": "0x1234",
    ///     "_pubkey": "Bitcoin public key (32 bytes)",
    ///     "signature": "Left(0x...)",
    ///     "_signature": "ECDSA signature",
    ///     "description": "Witness data for transaction ABC"
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
            // Skip special fields that are allowed for documentation/comments
            if name_str == "description" {
                // Top-level description for the entire witness file
                // Users can add comments here
                continue;
            }
            
            if name_str.starts_with("_") {
                // Convention: fields starting with _ are comments/hints
                // Examples: "_pubkey", "_signature", "_note"
                // These are completely ignored by the compiler
                continue;
            }

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
    /// Supports the same special fields as WitnessValues:
    /// - "description": Top-level comment for the arguments file (ignored)
    /// - "_<name>": Comments/hints for specific parameters (ignored)
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
    ///     "param_a": "42",
    ///     "_param_a": "Initial seed value",
    ///     "param_b": "0xabcd",
    ///     "_param_b": "Configuration flags",
    ///     "description": "Program arguments for initialization"
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
            // Skip special fields that are allowed for documentation/comments
            if name_str == "description" {
                // Top-level description for the entire arguments file
                continue;
            }
            
            if name_str.starts_with("_") {
                // Convention: fields starting with _ are comments/hints
                continue;
            }

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
    //
    // #[test]
    // fn witness_with_description_and_hints() {
    //     let json = r#"{
    //         "A": "42",
    //         "_A": "Important seed value",
    //         "description": "Test witness with comments"
    //     }"#;
    //     let witness_types = /* create WitnessTypes with A: u32 */;
    //     let witness = WitnessValues::from_json_with_types(json, &witness_types).unwrap();
    //     // Description and _A should be ignored, only A should be in witness
    //     assert_eq!(witness.iter().count(), 1);
    // }
}
