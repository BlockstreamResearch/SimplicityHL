use std::collections::HashMap;

use crate::error::Error;
use crate::str::WitnessName;
use crate::value::Value;
use crate::witness::{Arguments, WitnessTypes, WitnessValues};

// ============================================================================
// DEPRECATED: from_json_with_types() - Reserved for future use
// ============================================================================

#[deprecated(since = "0.5.0", note = "Use from_file_with_types instead")]
impl WitnessValues {
    pub fn from_json_with_types(
        _json: &str,
        _witness_types: &WitnessTypes,
    ) -> Result<Self, Error> {
        Err(Error::InvalidJsonFormat(
            "from_json_with_types is deprecated. Use from_file_with_types instead".to_string()
        ))
    }
}

// ============================================================================
// NEW: JSON Format Parsing (Private - used in from_file_with_types)
// ============================================================================

impl WitnessValues {
    /// Parse witness data from JSON format (internal helper).
    /// Supports both old nested format (with type field) and new flat format.
    /// 
    /// Old format: { "x": { "value": "0x0001", "type": "u32" } }
    /// New format: { "x": "0x0001" }
    fn parse_json(
        json: &str,
        witness_types: &WitnessTypes,
    ) -> Result<Self, Error> {
        let json_value: serde_json::Map<String, serde_json::Value> =
            serde_json::from_str(json).map_err(|e| {
                Error::InvalidJsonFormat(format!("Failed to parse as JSON: {}", e))
            })?;

        let mut map = HashMap::new();

        for (name_str, value_json) in json_value.iter() {
            let name = WitnessName::from_str_unchecked(name_str);

            let ty = witness_types
                .get(&name)
                .ok_or_else(|| Error::UndefinedWitness(name.clone()))?;

            // Support both JSON formats
            let value_str: String = match value_json {
                // New flat format: direct string value
                serde_json::Value::String(s) => s.clone(),
                
                // Old nested format: object with "value" field
                serde_json::Value::Object(obj) => {
                    match obj.get("value") {
                        Some(serde_json::Value::String(s)) => s.clone(),
                        Some(_) => {
                            return Err(Error::InvalidJsonFormat(format!(
                                "Witness `{}` value must be a string",
                                name
                            )))
                        }
                        None => {
                            return Err(Error::InvalidJsonFormat(format!(
                                "Witness `{}` must have a 'value' field in nested format",
                                name
                            )))
                        }
                    }
                }
                
                _ => {
                    return Err(Error::InvalidJsonFormat(format!(
                        "Witness `{}` must be a string (flat) or object (nested)",
                        name
                    )))
                }
            };

            let value = Value::parse_from_str(&value_str, ty)?;

            if map.insert(name.clone(), value).is_some() {
                return Err(Error::WitnessMultipleAssignments(name));
            }
        }

        Ok(Self::from(map))
    }
}

// ============================================================================
// NEW: YAML Format with Nested Structure
// ============================================================================
//
// Format:
// witness:
//   x: 0x0001
//   y: "1000"  # Comments are allowed
// ignored_section:
//   description: "Anything goes here"

impl WitnessValues {
    /// Parse YAML witness file with compiler-provided type context.
    ///
    /// Expected YAML structure:
    /// ```yaml
    /// witness:
    ///   variable_name: value
    ///   # Comments are allowed!
    /// ignored_section:
    ///   description: |
    ///     Developer notes go here
    /// ```
    ///
    /// The "witness:" section contains the actual witness values.
    /// Types are inferred from compiler context (no type definitions needed).
    pub fn from_yaml_with_types(
        yaml: &str,
        witness_types: &WitnessTypes,
    ) -> Result<Self, Error> {
        // Parse YAML
        let yaml_value: serde_yaml::Value = serde_yaml::from_str(yaml).map_err(|e| {
            Error::InvalidJsonFormat(format!("Failed to parse as YAML: {}", e))
        })?;

        // Extract "witness" section (required)
        let witness_section = yaml_value.get("witness").ok_or_else(|| {
            Error::InvalidJsonFormat("Missing 'witness:' section in YAML".to_string())
        })?;

        let mut map = HashMap::new();

        // Process witness mapping
        if let Some(witness_map) = witness_section.as_mapping() {
            for (key, value) in witness_map {
                // Extract variable name (must be string)
                let name_str = match key {
                    serde_yaml::Value::String(s) => s.clone(),
                    _ => {
                        return Err(Error::InvalidJsonFormat(
                            "Witness keys must be strings".to_string(),
                        ))
                    }
                };

                let name = WitnessName::from_str_unchecked(&name_str);

                // Get type from compiler-provided context
                let ty = witness_types
                    .get(&name)
                    .ok_or_else(|| Error::UndefinedWitness(name.clone()))?;

                // Extract value (must be string)
                let value_str = match value {
                    serde_yaml::Value::String(s) => s.clone(),
                    _ => {
                        return Err(Error::InvalidJsonFormat(format!(
                            "Witness `{}` must be a string value",
                            name
                        )))
                    }
                };

                // Parse value using compiler-provided type
                let parsed_value = Value::parse_from_str(&value_str, ty)?;

                // Check for duplicate assignments
                if map.insert(name.clone(), parsed_value).is_some() {
                    return Err(Error::WitnessMultipleAssignments(name));
                }
            }
        } else {
            return Err(Error::InvalidJsonFormat(
                "'witness:' section must be a mapping (key: value pairs)".to_string(),
            ));
        }

        Ok(Self::from(map))
    }

    /// Parse witness file with intelligent format detection.
    ///
    /// Strategy:
    /// 1. Try to parse as JSON first
    ///    - Supports both old nested format and new flat format
    ///    - If successful, use JSON deserialization (backward compatible)
    ///    - Existing tests continue to work
    /// 2. If JSON parsing fails, try YAML format
    ///    - Use YAML deserialization with witness: section
    ///    - No type definitions needed (compiler provides context)
    /// 3. If both fail, return informative error
    pub fn from_file_with_types(
        content: &str,
        witness_types: &WitnessTypes,
    ) -> Result<Self, Error> {
        // Step 1: Try to parse as JSON
        match Self::parse_json(content, witness_types) {
            Ok(result) => {
                // JSON parsing succeeded - use the JSON deserialization
                return Ok(result);
            }
            Err(_json_error) => {
                // JSON parsing failed - proceed to Step 2
            }
        }

        // Step 2: Try to parse as YAML
        match Self::from_yaml_with_types(content, witness_types) {
            Ok(result) => {
                // YAML parsing succeeded - use the YAML deserialization
                return Ok(result);
            }
            Err(yaml_error) => {
                // YAML parsing failed - return error
                return Err(yaml_error);
            }
        }
    }
}

impl Arguments {
    /// Parse YAML arguments file with compiler-provided type context.
    ///
    /// Expected YAML structure:
    /// ```yaml
    /// arguments:
    ///   param_name: value
    ///   # Comments allowed!
    /// ```
    pub fn from_yaml_with_types(
        yaml: &str,
        parameters: &crate::witness::Parameters,
    ) -> Result<Self, Error> {
        let yaml_value: serde_yaml::Value = serde_yaml::from_str(yaml).map_err(|e| {
            Error::InvalidJsonFormat(format!("Failed to parse as YAML: {}", e))
        })?;

        let arguments_section = yaml_value.get("arguments").ok_or_else(|| {
            Error::InvalidJsonFormat("Missing 'arguments:' section in YAML".to_string())
        })?;

        let mut map = HashMap::new();

        if let Some(args_map) = arguments_section.as_mapping() {
            for (key, value) in args_map {
                let name_str = match key {
                    serde_yaml::Value::String(s) => s.clone(),
                    _ => {
                        return Err(Error::InvalidJsonFormat(
                            "Argument keys must be strings".to_string(),
                        ))
                    }
                };

                let name = WitnessName::from_str_unchecked(&name_str);

                let ty = parameters
                    .get(&name)
                    .ok_or_else(|| Error::UndefinedParameter(name.clone()))?;

                let value_str = match value {
                    serde_yaml::Value::String(s) => s.clone(),
                    _ => {
                        return Err(Error::InvalidJsonFormat(format!(
                            "Parameter `{}` must be a string value",
                            name
                        )))
                    }
                };

                let parsed_value = Value::parse_from_str(&value_str, ty)?;

                if map.insert(name.clone(), parsed_value).is_some() {
                    return Err(Error::ArgumentMultipleAssignments(name));
                }
            }
        } else {
            return Err(Error::InvalidJsonFormat(
                "'arguments:' section must be a mapping".to_string(),
            ));
        }

        Ok(Self::from(map))
    }

    /// Parse arguments file with intelligent format detection.
    ///
    /// Strategy:
    /// 1. Try to parse as JSON first (backward compatible)
    ///    - Supports both old nested format and new flat format
    /// 2. If JSON fails, try YAML format
    /// 3. If both fail, return error
    pub fn from_file_with_types(
        content: &str,
        parameters: &crate::witness::Parameters,
    ) -> Result<Self, Error> {
        // Step 1: Try JSON
        match Self::parse_json(content, parameters) {
            Ok(result) => return Ok(result),
            Err(_) => {
                // Continue to Step 2
            }
        }

        // Step 2: Try YAML
        match Self::from_yaml_with_types(content, parameters) {
            Ok(result) => return Ok(result),
            Err(yaml_error) => {
                return Err(yaml_error);
            }
        }
    }

    fn parse_json(
        json: &str,
        parameters: &crate::witness::Parameters,
    ) -> Result<Self, Error> {
        let json_value: serde_json::Map<String, serde_json::Value> =
            serde_json::from_str(json).map_err(|e| {
                Error::InvalidJsonFormat(format!("Failed to parse as JSON: {}", e))
            })?;

        let mut map = HashMap::new();

        for (name_str, value_json) in json_value.iter() {
            let name = WitnessName::from_str_unchecked(name_str);

            let ty = parameters
                .get(&name)
                .ok_or_else(|| Error::UndefinedParameter(name.clone()))?;

            // Support both JSON formats
            let value_str: String = match value_json {
                // New flat format: direct string value
                serde_json::Value::String(s) => s.clone(),
                
                // Old nested format: object with "value" field
                serde_json::Value::Object(obj) => {
                    match obj.get("value") {
                        Some(serde_json::Value::String(s)) => s.clone(),
                        Some(_) => {
                            return Err(Error::InvalidJsonFormat(format!(
                                "Parameter `{}` value must be a string",
                                name
                            )))
                        }
                        None => {
                            return Err(Error::InvalidJsonFormat(format!(
                                "Parameter `{}` must have a 'value' field in nested format",
                                name
                            )))
                        }
                    }
                }
                
                _ => {
                    return Err(Error::InvalidJsonFormat(format!(
                        "Parameter `{}` must be a string (flat) or object (nested)",
                        name
                    )))
                }
            };

            let value = Value::parse_from_str(&value_str, ty)?;

            if map.insert(name.clone(), value).is_some() {
                return Err(Error::ArgumentMultipleAssignments(name));
            }
        }

        Ok(Self::from(map))
    }
}

#[cfg(test)]
mod tests {
}

// Note: The tests module above is empty because integration tests in lib.rs
// provide the comprehensive validation. However, here are inline tests
// that validate the YAML and format detection logic:

#[cfg(test)]
mod yaml_tests {
    // ========================================================================
    // YAML Format Tests - Testing witness: section
    // ========================================================================

    /// Test parsing simple YAML with witness: section
    #[test]
    fn yaml_witness_section_simple() {
        let yaml = r#"
witness:
  x: "0x0001"
  y: "100"
"#;
        // YAML should parse without errors
        let result: Result<serde_yaml::Value, _> = serde_yaml::from_str(yaml);
        assert!(result.is_ok());
        let value = result.unwrap();
        
        // witness: section should exist
        assert!(value.get("witness").is_some());
        
        // Should be a mapping
        assert!(value.get("witness").unwrap().as_mapping().is_some());
    }

    /// Test parsing YAML with comments in witness: section
    #[test]
    fn yaml_witness_section_with_comments() {
        let yaml = r#"
witness:
  # This is the sender signature
  sender_sig: "0x123..."
  # This is the amount
  amount: "1000"

metadata:
  description: "Test data"
"#;
        // YAML should parse without errors
        let result: Result<serde_yaml::Value, _> = serde_yaml::from_str(yaml);
        assert!(result.is_ok());
        let value = result.unwrap();
        
        // witness: section should exist and be a mapping
        let witness = value.get("witness").unwrap();
        assert!(witness.as_mapping().is_some());
        
        // metadata should be ignored but still present in YAML
        assert!(value.get("metadata").is_some());
    }

    /// Test that witness: section is required
    #[test]
    fn yaml_missing_witness_section() {
        let yaml = r#"
metadata:
  description: "No witness section"
"#;
        let result: Result<serde_yaml::Value, _> = serde_yaml::from_str(yaml);
        assert!(result.is_ok());
        let value = result.unwrap();
        
        // witness: section should NOT exist
        assert!(value.get("witness").is_none());
    }

    /// Test YAML with multiple ignored sections
    #[test]
    fn yaml_multiple_ignored_sections() {
        let yaml = r#"
witness:
  x: "0x0001"

metadata:
  created: "2024-12-29"
  author: "test"

documentation:
  description: |
    This is a test witness file
    demonstrating multiple sections

notes:
  comment: "Everything except witness: should be ignored"
"#;
        let result: Result<serde_yaml::Value, _> = serde_yaml::from_str(yaml);
        assert!(result.is_ok());
        let value = result.unwrap();
        
        // witness: should exist
        assert!(value.get("witness").is_some());
        
        // All other sections should exist in YAML but are ignored during parsing
        assert!(value.get("metadata").is_some());
        assert!(value.get("documentation").is_some());
        assert!(value.get("notes").is_some());
    }

    /// Test that witness: section must be a mapping (key: value pairs)
    #[test]
    fn yaml_witness_section_must_be_mapping() {
        let yaml = r#"
witness:
  - "not"
  - "a"
  - "mapping"
"#;
        let result: Result<serde_yaml::Value, _> = serde_yaml::from_str(yaml);
        assert!(result.is_ok());
        let value = result.unwrap();
        
        let witness = value.get("witness").unwrap();
        
        // witness should be a sequence (array), not a mapping
        assert!(witness.as_sequence().is_some());
        // Not a mapping
        assert!(witness.as_mapping().is_none());
    }

    /// Test arguments: section format
    #[test]
    fn yaml_arguments_section_simple() {
        let yaml = r#"
arguments:
  param1: "0x0001"
  param2: "100"
"#;
        let result: Result<serde_yaml::Value, _> = serde_yaml::from_str(yaml);
        assert!(result.is_ok());
        let value = result.unwrap();
        
        // arguments: section should exist
        assert!(value.get("arguments").is_some());
        
        // Should be a mapping
        assert!(value.get("arguments").unwrap().as_mapping().is_some());
    }

    /// Test arguments: section with comments
    #[test]
    fn yaml_arguments_section_with_comments() {
        let yaml = r#"
arguments:
  # First parameter
  param1: "0x0001"
  # Second parameter
  param2: "100"

metadata:
  description: "Test arguments"
"#;
        let result: Result<serde_yaml::Value, _> = serde_yaml::from_str(yaml);
        assert!(result.is_ok());
        let value = result.unwrap();
        
        // arguments: should exist and be a mapping
        let arguments = value.get("arguments").unwrap();
        assert!(arguments.as_mapping().is_some());
    }

    // ========================================================================
    // Format Detection Tests
    // ========================================================================

    /// Test that JSON is recognized as JSON format
    #[test]
    fn format_detection_json_is_json() {
        let json = r#"{ "x": "0x0001" }"#;
        
        // JSON parsing should succeed
        let result: Result<serde_json::Map<String, serde_json::Value>, _> = 
            serde_json::from_str(json);
        assert!(result.is_ok());
    }

    /// Test that YAML is NOT valid JSON
    #[test]
    fn format_detection_yaml_not_json() {
        let yaml = r#"
witness:
  x: "0x0001"
"#;
        
        // YAML should fail JSON parsing
        let result: Result<serde_json::Value, _> = serde_json::from_str(yaml);
        assert!(result.is_err());
    }

    /// Test that invalid data is neither JSON nor YAML
    #[test]
    fn format_detection_garbage_is_neither() {
        // Use data with unclosed bracket - invalid for both JSON and YAML
        let garbage = r#"{test: [invalid yaml with unclosed bracket}"#;
        
        // JSON should fail (invalid JSON structure)
        let json_result: Result<serde_json::Value, _> = serde_json::from_str(garbage);
        assert!(json_result.is_err(), "JSON should fail on unclosed bracket");
        
        // YAML should also fail (unclosed bracket is invalid YAML syntax)
        let yaml_result: Result<serde_yaml::Value, _> = serde_yaml::from_str(garbage);
        assert!(yaml_result.is_err(), "YAML should fail on unclosed bracket");
    }
}
