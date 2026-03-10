//! Library for parsing and compiling SimplicityHL

pub mod array;
pub mod ast;
pub mod compile;
pub mod debug;
pub mod driver;
pub mod dummy_env;
pub mod error;
pub mod jet;
pub mod lexer;
pub mod named;
pub mod num;
pub mod parse;
pub mod pattern;
#[cfg(feature = "serde")]
mod serde;
pub mod str;
pub mod tracker;
pub mod types;
pub mod value;
mod witness;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use simplicity::jet::elements::ElementsEnv;
use simplicity::{jet::Elements, CommitNode, RedeemNode};

pub extern crate either;
pub extern crate simplicity;
pub use simplicity::elements;

use crate::debug::DebugSymbols;
use crate::driver::ProjectGraph;
use crate::error::{Error, ErrorCollector, RichError, WithSource, WithSpan};
use crate::lexer::RESERVED_TOKENS;
use crate::parse::{ParseFromStrWithErrors, UseDecl};
pub use crate::types::ResolvedType;
pub use crate::value::Value;
pub use crate::witness::{Arguments, Parameters, WitnessTypes, WitnessValues};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SourceName {
    Real(Arc<Path>),
    Virtual(Arc<str>),
}

impl SourceName {
    pub fn without_extension(&self) -> SourceName {
        match self {
            SourceName::Real(path) => SourceName::Real(Arc::from(path.with_extension(""))),
            SourceName::Virtual(name) => SourceName::Virtual(name.clone()),
        }
    }
}

impl Default for SourceName {
    fn default() -> Self {
        SourceName::Virtual(Arc::from("<unnkown>"))
    }
}

use std::fmt;

impl fmt::Display for SourceName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceName::Real(path) => write!(f, "{}", path.display()),
            SourceName::Virtual(name) => write!(f, "{}", name),
        }
    }
}

/// Represents a source file containing code.
///
/// Groups the file's name and its content together to guarantee
/// they are always synchronized when present.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SourceFile {
    /// The name or path of the source file (e.g., "main.simf").
    name: SourceName,
    /// The actual text content of the source file.
    content: Arc<str>,
}

impl From<(SourceName, &str)> for SourceFile {
    fn from((name, content): (SourceName, &str)) -> Self {
        Self {
            name,
            content: Arc::from(content),
        }
    }
}

impl SourceFile {
    pub fn new(name: SourceName, content: Arc<str>) -> Self {
        Self { name, content }
    }

    pub fn name(&self) -> SourceName {
        self.name.clone()
    }

    pub fn content(&self) -> Arc<str> {
        self.content.clone()
    }
}

pub type LibTable = HashMap<String, PathBuf>;

pub fn get_full_path(libraries: &LibTable, use_decl: &UseDecl) -> Result<PathBuf, RichError> {
    let parts: Vec<&str> = use_decl.path().iter().map(|s| s.as_ref()).collect();

    let first_segment = match parts.first() {
        Some(s) => *s,
        None => {
            return Err(Error::CannotParse("Empty use path".to_string()))
                .with_span(*use_decl.span())
        }
    };

    if let Some(lib_root) = libraries.get(first_segment) {
        let mut full_path = lib_root.clone();
        full_path.extend(&parts[1..]);
        return Ok(full_path);
    }

    Err(Error::UnknownLibrary(first_segment.to_string())).with_span(*use_decl.span())
}

/// If something went wrong, then function was failed
fn is_reserved_tokens_in_aliases(libraries: &LibTable) -> Result<(), String> {
    for k in libraries.keys() {
        if RESERVED_TOKENS.contains(&k.as_str()) {
            return Err(format!(
                "Error: The identifier `{}` is a reserved keyword for intrinsic operations and cannot be utilized as a library name.",
                k
            ));
        }
    }
    Ok(())
}

/// The template of a SimplicityHL program.
///
/// A template has parameterized values that need to be supplied with arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TemplateProgram {
    simfony: ast::Program,
    source: SourceFile,
}

impl TemplateProgram {
    /// Parse the template of a SimplicityHL program.
    ///
    /// ## Errors
    ///
    /// The string is not a valid SimplicityHL program.
    pub fn new<Str: Into<Arc<str>>>(
        source_name: SourceName,
        libraries: Arc<LibTable>,
        s: Str,
    ) -> Result<Self, String> {
        is_reserved_tokens_in_aliases(&libraries)?;
        let source_name = source_name.without_extension();
        let file = s.into();
        let source = SourceFile::new(source_name.clone(), file.clone());

        // Create Global error_handler
        let mut error_handler = ErrorCollector::new();

        // 1. Parse root file
        let parsed_program =
            parse::Program::parse_from_str_with_errors(&file, source.clone(), &mut error_handler)
                .ok_or_else(|| error_handler.to_string())?;

        // 2. Create the driver program
        let driver_program: driver::Program = if libraries.is_empty() {
            driver::Program::from_parse(&parsed_program, source.clone(), &mut error_handler)
                .ok_or_else(|| error_handler.to_string())?
        } else {
            let graph = ProjectGraph::new(
                source.clone(),
                libraries,
                &parsed_program,
                &mut error_handler,
            )
            .ok_or_else(|| error_handler.to_string())?;

            graph
                .resolve_complication_order(&mut error_handler)?
                .ok_or_else(|| error_handler.to_string())?
        };

        // 3. AST Analysis
        let ast_program = ast::Program::analyze(&driver_program).with_source(source.clone())?;
        Ok(Self {
            simfony: ast_program,
            source,
        })
    }

    /// Access the parameters of the program.
    pub fn parameters(&self) -> &Parameters {
        self.simfony.parameters()
    }

    /// Access the witness types of the program.
    pub fn witness_types(&self) -> &WitnessTypes {
        self.simfony.witness_types()
    }

    /// Instantiate the template program with the given `arguments`.
    ///
    /// ## Errors
    ///
    /// The arguments are not consistent with the parameters of the program.
    /// Use [`TemplateProgram::parameters`] to see which parameters the program has.
    pub fn instantiate(
        &self,
        arguments: Arguments,
        include_debug_symbols: bool,
    ) -> Result<CompiledProgram, String> {
        arguments
            .is_consistent(self.simfony.parameters())
            .map_err(|error| error.to_string())?;

        let commit = self
            .simfony
            .compile(arguments, include_debug_symbols)
            .with_source(self.source.clone())?;

        Ok(CompiledProgram {
            debug_symbols: self.simfony.debug_symbols(self.source.content.as_ref()),
            simplicity: commit,
            witness_types: self.simfony.witness_types().shallow_clone(),
            parameter_types: self.simfony.parameters().shallow_clone(),
        })
    }

    pub fn generate_abi_meta(&self) -> Result<AbiMeta, String> {
        Ok(AbiMeta {
            witness_types: self.simfony.witness_types().shallow_clone(),
            param_types: self.parameters().shallow_clone(),
        })
    }
}

/// A SimplicityHL program, compiled to Simplicity.
#[derive(Clone, Debug)]
pub struct CompiledProgram {
    simplicity: Arc<named::CommitNode<Elements>>,
    witness_types: WitnessTypes,
    debug_symbols: DebugSymbols,
    parameter_types: Parameters,
}

impl CompiledProgram {
    /// Parse and compile a SimplicityHL program from the given string.
    ///
    /// ## See
    ///
    /// - [`TemplateProgram::new`]
    /// - [`TemplateProgram::instantiate`]
    pub fn new<Str: Into<Arc<str>>>(
        source_name: SourceName,
        libraries: Arc<LibTable>,
        s: Str,
        arguments: Arguments,
        include_debug_symbols: bool,
    ) -> Result<Self, String> {
        TemplateProgram::new(source_name, libraries, s)
            .and_then(|template| template.instantiate(arguments, include_debug_symbols))
    }

    /// Access the debug symbols for the Simplicity target code.
    pub fn debug_symbols(&self) -> &DebugSymbols {
        &self.debug_symbols
    }

    /// Access the Simplicity target code, without witness data.
    pub fn commit(&self) -> Arc<CommitNode<Elements>> {
        named::forget_names(&self.simplicity)
    }

    /// Satisfy the SimplicityHL program with the given `witness_values`.
    ///
    /// ## Errors
    ///
    /// - Witness values have a different type than declared in the SimplicityHL program.
    /// - There are missing witness values.
    pub fn satisfy(&self, witness_values: WitnessValues) -> Result<SatisfiedProgram, String> {
        self.satisfy_with_env(witness_values, None)
    }

    /// Satisfy the SimplicityHL program with the given `witness_values`.
    /// If `env` is `None`, the program is not pruned, otherwise it is pruned with the given environment.
    ///
    /// ## Errors
    ///
    /// - Witness values have a different type than declared in the SimplicityHL program.
    /// - There are missing witness values.
    pub fn satisfy_with_env(
        &self,
        witness_values: WitnessValues,
        env: Option<&ElementsEnv<Arc<elements::Transaction>>>,
    ) -> Result<SatisfiedProgram, String> {
        witness_values
            .is_consistent(&self.witness_types)
            .map_err(|e| e.to_string())?;

        let mut simplicity_redeem = named::populate_witnesses(&self.simplicity, witness_values)?;
        if let Some(env) = env {
            simplicity_redeem = simplicity_redeem.prune(env).map_err(|e| e.to_string())?;
        }
        Ok(SatisfiedProgram {
            simplicity: simplicity_redeem,
            debug_symbols: self.debug_symbols.clone(),
        })
    }

    pub fn generate_abi_meta(&self) -> Result<AbiMeta, String> {
        Ok(AbiMeta {
            witness_types: self.witness_types.shallow_clone(),
            param_types: self.parameter_types.shallow_clone(),
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AbiMeta {
    pub witness_types: WitnessTypes,
    pub param_types: Parameters,
}

/// A SimplicityHL program, compiled to Simplicity and satisfied with witness data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatisfiedProgram {
    simplicity: Arc<RedeemNode<Elements>>,
    debug_symbols: DebugSymbols,
}

impl SatisfiedProgram {
    /// Parse, compile and satisfy a SimplicityHL program from the given string.
    ///
    /// ## See
    ///
    /// - [`TemplateProgram::new`]
    /// - [`TemplateProgram::instantiate`]
    /// - [`CompiledProgram::satisfy`]
    pub fn new<Str: Into<Arc<str>>>(
        source_name: SourceName,
        libraries: Arc<LibTable>,
        s: Str,
        arguments: Arguments,
        witness_values: WitnessValues,
        include_debug_symbols: bool,
    ) -> Result<Self, String> {
        let compiled =
            CompiledProgram::new(source_name, libraries, s, arguments, include_debug_symbols)?;
        compiled.satisfy(witness_values)
    }

    /// Access the Simplicity target code, including witness data.
    pub fn redeem(&self) -> &Arc<RedeemNode<Elements>> {
        &self.simplicity
    }

    /// Access the debug symbols for the Simplicity target code.
    pub fn debug_symbols(&self) -> &DebugSymbols {
        &self.debug_symbols
    }
}

/// Recursively implement [`PartialEq`], [`Eq`] and [`std::hash::Hash`]
/// using selected members of a given type. The type must have a getter
/// method for each selected member.
#[macro_export]
macro_rules! impl_eq_hash {
    ($ty: ident; $($member: ident),*) => {
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                true $(&& self.$member() == other.$member())*
            }
        }

        impl Eq for $ty {}

        impl std::hash::Hash for $ty {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                $(self.$member().hash(state);)*
            }
        }
    };
}

/// Helper trait for implementing [`arbitrary::Arbitrary`] for recursive structures.
///
/// [`ArbitraryRec::arbitrary_rec`] allows the caller to set a budget that is decreased every time
/// the generated structure gets deeper. The maximum depth of the generated structure is equal to
/// the initial budget. The budget prevents the generated structure from becoming too deep, which
/// could cause issues in the code that processes these structures.
///
/// <https://github.com/rust-fuzz/arbitrary/issues/78>
#[cfg(feature = "arbitrary")]
trait ArbitraryRec: Sized {
    /// Generate a recursive structure from unstructured data.
    ///
    /// Generate leaves or parents when the budget is positive.
    /// Generate only leaves when the budget is zero.
    ///
    /// ## Implementation
    ///
    /// Recursive calls of [`arbitrary_rec`] must decrease the budget by one.
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self>;
}

/// Helper trait for implementing [`arbitrary::Arbitrary`] for typed structures.
///
/// [`arbitrary::Arbitrary`] is intended to produce well-formed values.
/// Structures with an internal type should be generated in a well-typed fashion.
///
/// [`arbitrary::Arbitrary`] can be implemented for a typed structure as follows:
/// 1. Generate the type via [`arbitrary::Arbitrary`].
/// 2. Generate the structure via [`ArbitraryOfType::arbitrary_of_type`].
#[cfg(feature = "arbitrary")]
pub trait ArbitraryOfType: Sized {
    /// Internal type of the structure.
    type Type;

    /// Generate a structure of the given type.
    fn arbitrary_of_type(
        u: &mut arbitrary::Unstructured,
        ty: &Self::Type,
    ) -> arbitrary::Result<Self>;
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::parse::ParseFromStr;
    use base64::display::Base64Display;
    use base64::engine::general_purpose::STANDARD;
    use simplicity::BitMachine;
    use std::borrow::Cow;
    use std::path::Path;

    use crate::*;

    pub(crate) struct TestCase<T> {
        program: T,
        lock_time: elements::LockTime,
        sequence: elements::Sequence,
        include_fee_output: bool,
    }

    impl TestCase<TemplateProgram> {
        pub fn template_file<P: AsRef<Path>>(program_file_path: P) -> Self {
            let program_text = std::fs::read_to_string(program_file_path).unwrap();
            Self::template_text(
                SourceName::default(),
                Arc::from(HashMap::new()),
                Cow::Owned(program_text),
            )
        }

        pub fn template_lib(
            source_name: SourceName,
            libraries: Arc<LibTable>,
            program_file: &Path,
        ) -> Self {
            let program_text = std::fs::read_to_string(program_file).unwrap();
            Self::template_text(source_name, libraries, Cow::Owned(program_text))
        }

        pub fn template_text(
            source_name: SourceName,
            libraries: Arc<LibTable>,
            program_text: Cow<str>,
        ) -> Self {
            let program = match TemplateProgram::new(source_name, libraries, program_text.as_ref())
            {
                Ok(x) => x,
                Err(error) => panic!("{error}"),
            };
            Self {
                program,
                lock_time: elements::LockTime::ZERO,
                sequence: elements::Sequence::MAX,
                include_fee_output: false,
            }
        }

        #[cfg(feature = "serde")]
        pub fn with_argument_file<P: AsRef<Path>>(
            self,
            arguments_file_path: P,
        ) -> TestCase<CompiledProgram> {
            let arguments_text = std::fs::read_to_string(arguments_file_path).unwrap();
            let arguments = match serde_json::from_str::<Arguments>(&arguments_text) {
                Ok(x) => x,
                Err(error) => panic!("{error}"),
            };
            self.with_arguments(arguments)
        }

        pub fn with_arguments(self, arguments: Arguments) -> TestCase<CompiledProgram> {
            let program = match self.program.instantiate(arguments, true) {
                Ok(x) => x,
                Err(error) => panic!("{error}"),
            };
            TestCase {
                program,
                lock_time: self.lock_time,
                sequence: self.sequence,
                include_fee_output: self.include_fee_output,
            }
        }
    }

    impl TestCase<CompiledProgram> {
        pub fn temp_env(
            main_content: &str,
            libs: Vec<(&str, &str, &str)>,
        ) -> (Self, tempfile::TempDir) {
            let temp_dir = tempfile::TempDir::new().unwrap();
            let main_path =
                driver::tests::create_simf_file(temp_dir.path(), "main.simf", main_content);
            let mut lib_paths = Vec::new();

            for (lib_name, rel_path, content) in libs {
                driver::tests::create_simf_file(temp_dir.path(), rel_path, content);

                let lib_root = temp_dir
                    .path()
                    .join(rel_path)
                    .parent()
                    .unwrap()
                    .to_path_buf();
                lib_paths.push((lib_name.to_string(), lib_root));
            }

            let libs_refs: Vec<(&str, &std::path::Path)> = lib_paths
                .iter()
                .map(|(k, v)| (k.as_str(), v.as_path()))
                .collect();

            let test_case = Self::program_file_with_libs(&main_path, libs_refs);
            (test_case, temp_dir)
        }

        pub fn program_file<P: AsRef<Path>>(program_file_path: P) -> Self {
            TestCase::<TemplateProgram>::template_file(program_file_path)
                .with_arguments(Arguments::default())
        }

        pub fn program_text(program_text: Cow<str>) -> Self {
            TestCase::<TemplateProgram>::template_text(
                SourceName::default(),
                Arc::from(HashMap::new()),
                program_text,
            )
            .with_arguments(Arguments::default())
        }

        pub fn program_file_with_libs<P, I, K, V>(program_file_path: P, libs: I) -> Self
        where
            P: AsRef<Path>,
            I: IntoIterator<Item = (K, V)>, // Magic trait: accepts anything we can iterate over
            K: Into<String>,
            V: AsRef<Path>,
        {
            let path_ref = program_file_path.as_ref();

            let mut libraries = HashMap::new();
            for (k, v) in libs {
                libraries.insert(k.into(), v.as_ref().to_path_buf());
            }

            let source_name =
                SourceName::Real(Arc::from(path_ref.parent().unwrap_or(Path::new(""))));

            // 3. Delegate to your existing template_lib method
            TestCase::<TemplateProgram>::template_lib(source_name, Arc::from(libraries), path_ref)
                .with_arguments(Arguments::default())
        }

        #[cfg(feature = "serde")]
        pub fn with_witness_file<P: AsRef<Path>>(
            self,
            witness_file_path: P,
        ) -> TestCase<SatisfiedProgram> {
            let witness_text = std::fs::read_to_string(witness_file_path).unwrap();
            let witness_values = match serde_json::from_str::<WitnessValues>(&witness_text) {
                Ok(x) => x,
                Err(error) => panic!("{error}"),
            };
            self.with_witness_values(witness_values)
        }

        pub fn with_witness_values(
            self,
            witness_values: WitnessValues,
        ) -> TestCase<SatisfiedProgram> {
            let program = match self.program.satisfy(witness_values) {
                Ok(x) => x,
                Err(error) => panic!("{error}"),
            };
            TestCase {
                program,
                lock_time: self.lock_time,
                sequence: self.sequence,
                include_fee_output: self.include_fee_output,
            }
        }

        pub fn get_encoding(self) -> String {
            let program_bytes = self.program.commit().to_vec_without_witness();
            Base64Display::new(&program_bytes, &STANDARD).to_string()
        }
    }

    impl<T> TestCase<T> {
        #[allow(dead_code)]
        pub fn with_lock_time(mut self, height: u32) -> Self {
            let height = elements::locktime::Height::from_consensus(height).unwrap();
            self.lock_time = elements::LockTime::Blocks(height);
            if self.sequence.is_final() {
                self.sequence = elements::Sequence::ENABLE_LOCKTIME_NO_RBF;
            }
            self
        }

        #[allow(dead_code)]
        pub fn with_sequence(mut self, distance: u16) -> Self {
            self.sequence = elements::Sequence::from_height(distance);
            self
        }

        #[allow(dead_code)]
        pub fn print_sighash_all(self) -> Self {
            let env = dummy_env::dummy_with(self.lock_time, self.sequence, self.include_fee_output);
            dbg!(env.c_tx_env().sighash_all());
            self
        }
    }

    impl TestCase<SatisfiedProgram> {
        #[allow(dead_code)]
        pub fn print_encoding(self) -> Self {
            let (program_bytes, witness_bytes) = self.program.redeem().to_vec_with_witness();
            println!(
                "Program:\n{}",
                Base64Display::new(&program_bytes, &STANDARD)
            );
            println!(
                "Witness:\n{}",
                Base64Display::new(&witness_bytes, &STANDARD)
            );
            self
        }

        fn run(self) -> Result<(), simplicity::bit_machine::ExecutionError> {
            let env = dummy_env::dummy_with(self.lock_time, self.sequence, self.include_fee_output);
            let pruned = self.program.redeem().prune(&env)?;
            let mut mac = BitMachine::for_program(&pruned)
                .expect("program should be within reasonable bounds");
            mac.exec(&pruned, &env).map(|_| ())
        }

        pub fn assert_run_success(self) {
            match self.run() {
                Ok(()) => {}
                Err(error) => panic!("Unexpected error: {error}"),
            }
        }

        pub fn get_encoding_with_witness(self) -> (String, String) {
            let (program_bytes, witness_bytes) = self.program.redeem().to_vec_with_witness();
            (
                Base64Display::new(&program_bytes, &STANDARD).to_string(),
                Base64Display::new(&witness_bytes, &STANDARD).to_string(),
            )
        }
    }

    const VALID_TESTS_DIR: &str = "./functional-tests/valid-test-cases";
    const ERROR_TESTS_DIR: &str = "./functional-tests/error-test-cases";

    // Real test cases
    #[test]
    fn module_simple() {
        TestCase::program_file_with_libs(
            format!("{}/module-simple/main.simf", VALID_TESTS_DIR),
            [("lib", format!("{}/module-simple/lib", VALID_TESTS_DIR))],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    fn diamond_dependency_resolution() {
        TestCase::program_file_with_libs(
            format!(
                "{}/diamond-dependency-resolution/main.simf",
                VALID_TESTS_DIR
            ),
            [(
                "lib",
                format!("{}/diamond-dependency-resolution/lib", VALID_TESTS_DIR),
            )],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    #[should_panic(expected = "Circular dependency detected:")]
    fn cyclic_dependency_error() {
        TestCase::program_file_with_libs(
            format!("{}/cyclic-dependency/main.simf", ERROR_TESTS_DIR),
            [("lib", format!("{}/cyclic-dependency/lib", ERROR_TESTS_DIR))],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    fn deep_reexport_chain() {
        TestCase::program_file_with_libs(
            format!("{}/deep-reexport-chain/main.simf", VALID_TESTS_DIR),
            [(
                "lib",
                format!("{}/deep-reexport-chain/lib", VALID_TESTS_DIR),
            )],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    #[should_panic(expected = "Item `SecretType` is private")]
    fn private_type_visibility_error() {
        TestCase::program_file_with_libs(
            format!("{}/private-visibility/main.simf", ERROR_TESTS_DIR),
            [("lib", format!("{}/private-visibility/lib", ERROR_TESTS_DIR))],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    #[should_panic(
        expected = "Error: The identifier `jet` is a reserved keyword for intrinsic operations and cannot be utilized as a library name."
    )]
    fn using_jet_as_module() {
        let main_code = r#"
            use jet::eq_32::SecretType;
            fn main() {}
        "#;

        let libs = vec![(
            "jet",
            "temp/eq_32.simf",
            "type SecretType = u32; pub fn ok() {}",
        )];

        let (test, _dir) = TestCase::temp_env(main_code, libs);
        test.with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[test]
    fn single_lib() {
        TestCase::program_file_with_libs(
            "./examples/single_lib/main.simf",
            [("temp", "./examples/single_lib/temp")],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    #[should_panic(
        expected = "Cannot parse: found '*' expected '/', jet, witness, param, 'a', 'p', 'd', 'l', identifier, '0', something else, '-', '=', ':', ';', ',', '(', ')', '[', ']', '{', '}', '<', or '>'"
    )]
    fn global_import_error() {
        TestCase::program_file_with_libs(
            format!("{}/global/main.simf", ERROR_TESTS_DIR),
            [("lib", format!("{}/global/lib", ERROR_TESTS_DIR))],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    fn file_not_found_error() {
        use std::panic;
        let result = panic::catch_unwind(|| {
            TestCase::program_file_with_libs(
                format!("{}/file-not-found/main.simf", ERROR_TESTS_DIR),
                [("lib", &format!("{}/file-not-found/lib", ERROR_TESTS_DIR))],
            )
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
        });

        let panic_msg = result
            .err()
            .and_then(|b| b.downcast_ref::<String>().cloned())
            .unwrap_or_default();
        let expected = format!(
            "File `{}/file-not-found/lib/module.simf` not found",
            ERROR_TESTS_DIR
        );

        assert!(panic_msg.contains(&expected));
    }

    #[test]
    fn lib_not_found_error() {
        use std::panic;

        let result = panic::catch_unwind(|| {
            TestCase::program_file_with_libs(
                format!("{}/lib-not-found/main.simf", ERROR_TESTS_DIR),
                [("lib", &format!("{}/lib-not-found/lib", ERROR_TESTS_DIR))],
            )
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
        });

        let panic_msg = result
            .err()
            .and_then(|b| b.downcast_ref::<String>().cloned())
            .unwrap_or_default();
        let expected = format!(
            "File `{}/lib-not-found/lib/module.simf` not found",
            ERROR_TESTS_DIR
        );

        assert!(panic_msg.contains(&expected));
    }

    #[test]
    fn multi_lib_facade_resolution() {
        TestCase::program_file_with_libs(
            format!("{}/multi-lib-facade/main.simf", VALID_TESTS_DIR),
            [
                ("math", format!("{}/multi-lib-facade/math", VALID_TESTS_DIR)),
                (
                    "crypto",
                    format!("{}/multi-lib-facade/crypto", VALID_TESTS_DIR),
                ),
                ("api", format!("{}/multi-lib-facade/api", VALID_TESTS_DIR)),
            ],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    #[should_panic(expected = "Inconsistent resolution order")]
    fn cross_wire_linearization_error() {
        TestCase::program_file_with_libs(
            format!("{}/cross-wire/main.simf", ERROR_TESTS_DIR),
            [("lib", format!("{}/cross-wire/lib", ERROR_TESTS_DIR))],
        )
        .with_witness_values(WitnessValues::default())
        .assert_run_success();
    }

    #[test]
    fn cat() {
        TestCase::program_file("./examples/cat.simf")
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[test]
    fn ctv() {
        TestCase::program_file("./examples/ctv.simf")
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[test]
    fn regression_153() {
        TestCase::program_file("./examples/array_fold_2n.simf")
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn sighash_non_interactive_fee_bump() {
        let mut t = TestCase::program_file("./examples/non_interactive_fee_bump.simf")
            .with_witness_file("./examples/non_interactive_fee_bump.wit");
        t.sequence = elements::Sequence::ENABLE_LOCKTIME_NO_RBF;
        t.lock_time = elements::LockTime::from_time(1734967235 + 600).unwrap();
        t.include_fee_output = true;
        t.assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn escrow_with_delay_timeout() {
        TestCase::program_file("./examples/escrow_with_delay.simf")
            .with_sequence(1000)
            .print_sighash_all()
            .with_witness_file("./examples/escrow_with_delay.timeout.wit")
            .assert_run_success();
    }

    #[test]
    fn hash_loop() {
        TestCase::program_file("./examples/hash_loop.simf")
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn hodl_vault() {
        TestCase::program_file("./examples/hodl_vault.simf")
            .with_lock_time(1000)
            .print_sighash_all()
            .with_witness_file("./examples/hodl_vault.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn htlc_complete() {
        TestCase::program_file("./examples/htlc.simf")
            .print_sighash_all()
            .with_witness_file("./examples/htlc.complete.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn last_will_inherit() {
        TestCase::program_file("./examples/last_will.simf")
            .with_sequence(25920)
            .print_sighash_all()
            .with_witness_file("./examples/last_will.inherit.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn p2ms() {
        TestCase::program_file("./examples/p2ms.simf")
            .print_sighash_all()
            .with_witness_file("./examples/p2ms.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn p2pk() {
        TestCase::template_file("./examples/p2pk.simf")
            .with_argument_file("./examples/p2pk.args")
            .print_sighash_all()
            .with_witness_file("./examples/p2pk.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn p2pkh() {
        TestCase::program_file("./examples/p2pkh.simf")
            .print_sighash_all()
            .with_witness_file("./examples/p2pkh.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn presigned_vault_complete() {
        TestCase::program_file("./examples/presigned_vault.simf")
            .with_sequence(1000)
            .print_sighash_all()
            .with_witness_file("./examples/presigned_vault.complete.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn sighash_all_anyonecanpay() {
        TestCase::program_file("./examples/sighash_all_anyonecanpay.simf")
            .with_witness_file("./examples/sighash_all_anyonecanpay.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn sighash_all_anyprevout() {
        TestCase::program_file("./examples/sighash_all_anyprevout.simf")
            .with_witness_file("./examples/sighash_all_anyprevout.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn sighash_all_anyprevoutanyscript() {
        TestCase::program_file("./examples/sighash_all_anyprevoutanyscript.simf")
            .with_witness_file("./examples/sighash_all_anyprevoutanyscript.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn sighash_none() {
        TestCase::program_file("./examples/sighash_none.simf")
            .with_witness_file("./examples/sighash_none.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn sighash_single() {
        TestCase::program_file("./examples/sighash_single.simf")
            .with_witness_file("./examples/sighash_single.wit")
            .assert_run_success();
    }

    #[test]
    #[cfg(feature = "serde")]
    fn transfer_with_timeout_transfer() {
        TestCase::program_file("./examples/transfer_with_timeout.simf")
            .print_sighash_all()
            .with_witness_file("./examples/transfer_with_timeout.transfer.wit")
            .assert_run_success();
    }

    #[test]
    fn redefined_variable() {
        let prog_text = r#"fn main() {
    let beefbabe: (u16, u16) = (0xbeef, 0xbabe);
    let beefbabe: u32 = <(u16, u16)>::into(beefbabe);
}
"#;
        TestCase::program_text(Cow::Borrowed(prog_text))
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[test]
    fn empty_function_body_nonempty_return() {
        let prog_text = r#"fn my_true() -> bool {
    // function body is empty, although function must return `bool`
}

fn main() {
    assert!(my_true());
}
"#;
        match SatisfiedProgram::new(
            SourceName::default(),
            Arc::from(HashMap::new()),
            prog_text,
            Arguments::default(),
            WitnessValues::default(),
            false,
        ) {
            Ok(_) => panic!("Accepted faulty program"),
            Err(error) => {
                assert!(
                    error.contains("Expected expression of type `bool`, found type `()`"),
                    "Unexpected error: {error}",
                );
            }
        }
    }

    #[test]
    fn fuzz_regression_2() {
        parse::Program::parse_from_str("fn dbggscas(h: bool, asyxhaaaa: a) {\nfalse}\n\n").unwrap();
    }

    #[test]
    fn fuzz_slow_unit_1() {
        parse::Program::parse_from_str("fn fnnfn(MMet:(((sssss,((((((sssss,ssssss,ss,((((((sssss,ss,((((((sssss,ssssss,ss,((((((sssss,ssssss,((((((sssss,sssssssss,(((((((sssss,sssssssss,(((((ssss,((((((sssss,sssssssss,(((((((sssss,ssss,((((((sssss,ss,((((((sssss,ssssss,ss,((((((sssss,ssssss,((((((sssss,sssssssss,(((((((sssss,sssssssss,(((((ssss,((((((sssss,sssssssss,(((((((sssss,sssssssssssss,(((((((((((u|(").unwrap_err();
    }

    #[test]
    fn type_alias() {
        let prog_text = r#"type MyAlias = u32;

fn main() {
    let x: MyAlias = 32;
    assert!(jet::eq_32(x, 32));
}"#;
        TestCase::program_text(Cow::Borrowed(prog_text))
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[test]
    fn type_error_regression() {
        let prog_text = r#"fn main() {
    let (a, b): (u32, u32) = (0, 1);
    assert!(jet::eq_32(a, 0));

    let (c, d): (u32, u32) = (2, 3);
    assert!(jet::eq_32(c, 2));
    assert!(jet::eq_32(d, 3));
}"#;
        TestCase::program_text(Cow::Borrowed(prog_text))
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }

    #[cfg(feature = "serde")]
    mod regression {
        use super::TestCase;

        #[derive(serde::Deserialize)]
        struct Program {
            program: String,
            witness: Option<String>,
        }

        fn regression_test(name: &str) {
            let program = serde_json::from_str::<Program>(
                std::fs::read_to_string(format!("./test-data/{}.json", name))
                    .unwrap()
                    .as_str(),
            )
            .unwrap();

            let test_case = TestCase::program_file(format!("./examples/{}.simf", name));
            match program.witness {
                Some(wit) => {
                    let (new_program, new_witness) = test_case
                        .with_witness_file(format!("./examples/{}.wit", name))
                        .get_encoding_with_witness();
                    assert_eq!(
                        program.program, new_program,
                        "Byte code of programs should be the same"
                    );
                    assert_eq!(
                        wit, new_witness,
                        "Byte code of witnesses should be the same"
                    );
                }
                None => {
                    let new_program = test_case.get_encoding();

                    assert_eq!(
                        program.program, new_program,
                        "Byte code of programs should be the same"
                    )
                }
            }
        }

        #[test]
        fn array_fold_2n_regression() {
            regression_test("array_fold_2n");
        }

        #[test]
        fn array_fold_regression() {
            regression_test("array_fold");
        }

        #[test]
        fn cat_regression() {
            regression_test("cat");
        }

        #[test]
        fn ctv_regression() {
            regression_test("ctv");
        }

        #[test]
        fn escrow_with_delay_regression() {
            regression_test("escrow_with_delay");
        }

        #[test]
        fn hash_loop_regression() {
            regression_test("hash_loop");
        }

        #[test]
        fn hodl_vault_regression() {
            regression_test("hodl_vault");
        }

        #[test]
        fn htlc_regression() {
            regression_test("htlc");
        }

        #[test]
        fn last_will_regression() {
            regression_test("last_will");
        }

        #[test]
        fn non_interactive_fee_bump_regression() {
            regression_test("non_interactive_fee_bump");
        }

        #[test]
        fn p2ms_regression() {
            regression_test("p2ms");
        }

        #[test]
        fn p2pkh_regression() {
            regression_test("p2pkh");
        }

        #[test]
        fn presigned_vault_regression() {
            regression_test("presigned_vault");
        }

        #[test]
        fn reveal_collision_regression() {
            regression_test("reveal_collision");
        }

        #[test]
        fn reveal_fix_point_regression() {
            regression_test("reveal_fix_point");
        }

        #[test]
        fn sighash_all_anyonecanpay_regression() {
            regression_test("sighash_all_anyonecanpay");
        }

        #[test]
        fn sighash_all_anyprevoutanyscript_regression() {
            regression_test("sighash_all_anyprevoutanyscript");
        }

        #[test]
        fn sighash_all_anyprevout_regression() {
            regression_test("sighash_all_anyprevout");
        }

        #[test]
        fn sighash_none_regression() {
            regression_test("sighash_none");
        }

        #[test]
        fn sighash_single_regression() {
            regression_test("sighash_single");
        }

        #[test]
        fn transfer_with_timeout_regression() {
            regression_test("transfer_with_timeout");
        }
    }
}
