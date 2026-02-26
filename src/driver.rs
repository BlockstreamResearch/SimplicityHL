use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::parse::{self, ParseFromStrWithErrors, Visibility};
use crate::str::{AliasName, FunctionName, Identifier};
use crate::types::AliasedType;
use crate::{get_full_path, impl_eq_hash, LibTable, SourceFile, SourceName};

/// Represents a single, isolated file in the SimplicityHL project.
/// In this architecture, a file and a module are the exact same thing.
#[derive(Debug, Clone)]
pub struct Module {
    pub source: SourceFile,
    /// The completely parsed program for this specific file.
    /// it contains all the functions, aliases, and imports defined inside the file.
    pub parsed_program: parse::Program,
}

/// The Dependency Graph itself.
pub struct ProjectGraph {
    /// Arena Pattern: the data itself lives here.
    /// A flat vector guarantees that module data is stored contiguously in memory.
    pub(self) modules: Vec<Module>,

    /// The configuration environment.
    /// Used to resolve xternal library dependencies and invoke their associated functions.
    pub libraries: Arc<LibTable>,

    /// Fast lookup: `SourceName` -> Module ID.
    /// A reverse index mapping absolute file paths to their internal IDs.
    /// This solves the duplication problem, ensuring each file is only parsed once.
    pub lookup: HashMap<SourceName, usize>,

    /// Fast lookup: Module ID -> `SourceName`.
    /// A direct index mapping internal IDs back to their absolute file paths.
    /// This serves as the exact inverse of the `lookup` map.
    pub paths: Arc<[SourceName]>,

    /// The Adjacency List: Defines the Directed acyclic Graph (DAG) of imports.
    ///
    /// The Key (`usize`) is the ID of a "Parent" module (the file doing the importing).
    /// The Value (`Vec<usize>`) is a list of IDs of the "Child" modules it relies on.
    ///
    /// Example: If `main.simf` (ID: 0) has `use lib::math;` (ID: 1) and `use lib::io;` (ID: 2),
    /// this map will contain: `{ 0: [1, 2] }`.
    pub dependencies: HashMap<usize, Vec<usize>>,
}

// TODO: @LesterEvSe, Consider to change BTreeMap to BTreeSet here
pub type FileResolutions = BTreeMap<Identifier, Resolution>;

pub type ProgramResolutions = Arc<[FileResolutions]>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Resolution {
    pub visibility: Visibility,
}

#[derive(Clone, Debug)]
pub struct Program {
    items: Arc<[Item]>,
    paths: Arc<[SourceName]>,

    // Use BTreeMap instead of HashMap for the impl_eq_hash! macro.
    resolutions: ProgramResolutions,
    span: Span,
}

impl Program {
    pub fn from_parse(
        parsed: &parse::Program,
        source: SourceFile,
        handler: &mut ErrorCollector,
    ) -> Option<Self> {
        let root_path = source.name().without_extension();

        let mut items: Vec<Item> = Vec::new();
        let mut resolutions: Vec<FileResolutions> = vec![BTreeMap::new()];

        let main_file_id = 0usize;
        let mut errors: Vec<RichError> = Vec::new();

        for item in parsed.items() {
            match item {
                parse::Item::Use(use_decl) => {
                    let bug_report = RichError::new(
                        Error::UnknownLibrary(use_decl.path_buf().to_string_lossy().to_string()),
                        *use_decl.span(),
                    );
                    handler.push(bug_report);
                }
                parse::Item::TypeAlias(alias) => {
                    if let Some(err) = ProjectGraph::register_def(
                        &mut items,
                        &mut resolutions,
                        main_file_id,
                        item,
                        alias.name().clone().into(),
                        &parse::Visibility::Public,
                    ) {
                        errors.push(err)
                    }
                }
                parse::Item::Function(function) => {
                    if let Some(err) = ProjectGraph::register_def(
                        &mut items,
                        &mut resolutions,
                        main_file_id,
                        item,
                        function.name().clone().into(),
                        &parse::Visibility::Public,
                    ) {
                        errors.push(err);
                    }
                }
                parse::Item::Module => {}
            }
        }
        handler.update_with_source_enrichment(source, errors);

        if handler.has_errors() {
            None
        } else {
            Some(Program {
                items: items.into(),
                paths: Arc::from([root_path]),
                resolutions: resolutions.into(),
                span: *parsed.as_ref(),
            })
        }
    }

    /// Access the items of the program.
    pub fn items(&self) -> &[Item] {
        &self.items
    }

    /// Access the paths of the program
    pub fn paths(&self) -> &[SourceName] {
        &self.paths
    }

    /// Access the scope items of the program.
    pub fn resolutions(&self) -> &[FileResolutions] {
        &self.resolutions
    }
}

impl_eq_hash!(Program; items, paths, resolutions);

/// An item is a component of a driver Program
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Item {
    /// A type alias.
    TypeAlias(TypeAlias),
    /// A function.
    Function(Function),
    /// A module, which is ignored.
    Module,
}

impl Item {
    pub fn from_parse(parsed: &parse::Item, file_id: usize) -> Result<Self, RichError> {
        match parsed {
            parse::Item::TypeAlias(alias) => {
                let driver_alias = TypeAlias::from_parse(alias);
                Ok(Item::TypeAlias(driver_alias))
            }
            parse::Item::Function(func) => {
                let driver_func = Function::from_parse(func, file_id);
                Ok(Item::Function(driver_func))
            }
            parse::Item::Module => Ok(Item::Module),
            parse::Item::Use(use_decl) => {
                Err(RichError::new(
                    Error::Internal("Encountered 'Use' item during driver generation. Imports should be resolved by ProjectGraph.".to_string()),
                    *use_decl.span(),
                ))
            },
        }
    }
}

/// Definition of a function.
#[derive(Clone, Debug)]
pub struct Function {
    file_id: usize,
    name: FunctionName,
    params: Arc<[parse::FunctionParam]>,
    ret: Option<AliasedType>,
    body: parse::Expression,
    span: Span,
}

impl Function {
    /// Converts a parser function to a driver function.
    ///
    /// We explicitly pass `file_id` here because the `parse::Function`
    /// doesn't know which file it came from.
    pub fn from_parse(parsed: &parse::Function, file_id: usize) -> Self {
        Self {
            file_id,
            name: parsed.name().clone(),
            params: Arc::from(parsed.params()),
            ret: parsed.ret().cloned(),
            body: parsed.body().clone(),
            span: *parsed.as_ref(),
        }
    }

    /// Access the file id of the function.
    pub fn file_id(&self) -> usize {
        self.file_id
    }

    /// Access the name of the function.
    pub fn name(&self) -> &FunctionName {
        &self.name
    }

    /// Access the parameters of the function.
    pub fn params(&self) -> &[parse::FunctionParam] {
        &self.params
    }

    /// Access the return type of the function.
    ///
    /// An empty return type means that the function returns the unit value.
    pub fn ret(&self) -> Option<&AliasedType> {
        self.ret.as_ref()
    }

    /// Access the body of the function.
    pub fn body(&self) -> &parse::Expression {
        &self.body
    }

    /// Access the span of the function.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Function; file_id, name, params, ret, body);

// A type alias.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct TypeAlias {
    name: AliasName,
    ty: AliasedType,
    span: Span,
}

impl TypeAlias {
    /// Converts a parser function to a driver function.
    ///
    /// We explicitly pass `file_id` here because the `parse::Function`
    /// doesn't know which file it came from.
    pub fn from_parse(parsed: &parse::TypeAlias) -> Self {
        Self {
            name: parsed.name().clone(),
            ty: parsed.ty().clone(),
            span: *parsed.as_ref(),
        }
    }

    /// Access the name of the alias.
    pub fn name(&self) -> &AliasName {
        &self.name
    }

    /// Access the type that the alias resolves to.
    ///
    /// During the parsing stage, the resolved type may include aliases.
    /// The compiler will later check if all contained aliases have been declared before.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the span of the alias.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(TypeAlias; name, ty);

#[derive(Debug)]
pub enum C3Error {
    CycleDetected(Vec<usize>),
    InconsistentLinearization { module: usize },
}

impl ProjectGraph {
    fn parse_and_get_program(
        full_path: &Path,
        importer_source: SourceFile,
        span: Span,
        handler: &mut ErrorCollector,
    ) -> Option<Module> {
        let dep_key = SourceName::Real(Arc::from(full_path.with_extension("")));
        let Ok(content) = std::fs::read_to_string(full_path) else {
            let err = RichError::new(Error::FileNotFound(PathBuf::from(full_path)), span)
                .with_source(importer_source.clone());

            handler.push(err);
            return None;
        };

        let dep_source_file = SourceFile::new(dep_key.clone(), Arc::from(content.clone()));

        parse::Program::parse_from_str_with_errors(&content, dep_source_file.clone(), handler).map(
            |parsed_program| Module {
                source: dep_source_file,
                parsed_program,
            },
        )
    }

    pub fn new(
        root_source: SourceFile,
        libraries: Arc<LibTable>,
        root_program: &parse::Program,
        handler: &mut ErrorCollector,
    ) -> Option<Self> {
        let root_name_no_ext = root_source.name().without_extension();

        let mut modules: Vec<Module> = vec![Module {
            source: root_source,
            parsed_program: root_program.clone(),
        }];

        let mut lookup: HashMap<SourceName, usize> = HashMap::new();
        let mut paths: Vec<SourceName> = vec![root_name_no_ext.clone()];
        let mut dependencies: HashMap<usize, Vec<usize>> = HashMap::new();

        let root_id = 0;
        lookup.insert(root_name_no_ext, root_id);
        dependencies.insert(root_id, Vec::new());

        // Implementation of the standard BFS algorithm with memoization and queue
        let mut queue = VecDeque::new();
        queue.push_back(root_id);

        while let Some(curr_id) = queue.pop_front() {
            // We need this to report errors inside THIS file.
            let importer_source = modules[curr_id].source.clone();
            let current_program = &modules[curr_id].parsed_program;

            // Lists to separate valid logic from errors
            let mut valid_imports: Vec<(PathBuf, Span)> = Vec::new();
            let mut resolution_errors: Vec<RichError> = Vec::new();

            // PHASE 1: Resolve Imports
            for elem in current_program.items() {
                if let parse::Item::Use(use_decl) = elem {
                    match get_full_path(&libraries, use_decl) {
                        Ok(path) => valid_imports.push((path, *use_decl.span())),
                        Err(err) => {
                            resolution_errors.push(err.with_source(importer_source.clone()))
                        }
                    }
                }
            }

            // Phase 2: Load and Parse Dependencies
            for (path, import_span) in valid_imports {
                let full_path = path.with_extension("simf");
                let dep_source_name = SourceName::Real(Arc::from(full_path.as_path()));
                let dep_key = dep_source_name.without_extension();

                if let Some(&existing_id) = lookup.get(&dep_key) {
                    let deps = dependencies.entry(curr_id).or_default();
                    if !deps.contains(&existing_id) {
                        deps.push(existing_id);
                    }
                    continue;
                }

                let Some(module) = ProjectGraph::parse_and_get_program(
                    &full_path,
                    importer_source.clone(),
                    import_span,
                    handler,
                ) else {
                    continue;
                };

                let last_ind = modules.len();
                modules.push(module);

                lookup.insert(dep_key.clone(), last_ind);
                paths.push(dep_key);
                dependencies.entry(curr_id).or_default().push(last_ind);

                queue.push_back(last_ind);
            }
        }

        if handler.has_errors() {
            None
        } else {
            Some(Self {
                modules,
                libraries,
                lookup,
                paths: paths.into(),
                dependencies,
            })
        }
    }

    pub fn c3_linearize(&self) -> Result<Vec<usize>, C3Error> {
        self.linearize_module(0)
    }

    fn linearize_module(&self, root: usize) -> Result<Vec<usize>, C3Error> {
        let mut memo = HashMap::<usize, Vec<usize>>::new();
        let mut visiting = Vec::<usize>::new();

        self.linearize_rec(root, &mut memo, &mut visiting)
    }

    fn linearize_rec(
        &self,
        module: usize,
        memo: &mut HashMap<usize, Vec<usize>>,
        visiting: &mut Vec<usize>,
    ) -> Result<Vec<usize>, C3Error> {
        if let Some(result) = memo.get(&module) {
            return Ok(result.clone());
        }

        if visiting.contains(&module) {
            let cycle_start = visiting.iter().position(|m| *m == module).unwrap();
            return Err(C3Error::CycleDetected(visiting[cycle_start..].to_vec()));
        }

        visiting.push(module);

        let parents = self.dependencies.get(&module).cloned().unwrap_or_default();

        let mut seqs: Vec<Vec<usize>> = Vec::new();

        for parent in &parents {
            let lin = self.linearize_rec(*parent, memo, visiting)?;
            seqs.push(lin);
        }

        seqs.push(parents.clone());

        let mut result = vec![module];
        let merged = merge(seqs).ok_or(C3Error::InconsistentLinearization { module })?;

        result.extend(merged);

        visiting.pop();
        memo.insert(module, result.clone());

        Ok(result)
    }

    fn process_use_item(
        resolutions: &mut [FileResolutions],
        file_id: usize,
        ind: usize,
        elem: &Identifier,
        use_decl: &parse::UseDecl,
    ) -> Option<RichError> {
        let Some(resolution) = resolutions[ind].get(elem) else {
            return Some(RichError::new(
                Error::UnresolvedItem(elem.as_inner().to_string()),
                *use_decl.span(),
            ));
        };

        if matches!(resolution.visibility, parse::Visibility::Private) {
            return Some(RichError::new(
                Error::PrivateItem(elem.as_inner().to_string()),
                *use_decl.span(),
            ));
        }

        resolutions[file_id].insert(
            elem.clone(),
            Resolution {
                visibility: use_decl.visibility().clone(),
            },
        );

        None
    }

    fn register_def(
        items: &mut Vec<Item>,
        resolutions: &mut [FileResolutions],
        file_id: usize,
        item: &parse::Item,
        name: Identifier,
        vis: &parse::Visibility,
    ) -> Option<RichError> {
        let item = match Item::from_parse(item, file_id) {
            Ok(item) => item,
            Err(err) => return Some(err),
        };

        items.push(item);
        resolutions[file_id].insert(
            name,
            Resolution {
                visibility: vis.clone(),
            },
        );

        None
    }

    fn build_program(&self, order: &Vec<usize>, handler: &mut ErrorCollector) -> Option<Program> {
        let mut items: Vec<Item> = Vec::new();
        let mut resolutions: Vec<FileResolutions> = vec![BTreeMap::new(); order.len()];

        for &file_id in order {
            let importer_source = self.modules[file_id].source.clone();
            let program_items = self.modules[file_id].parsed_program.items();

            for elem in program_items {
                let mut errors: Vec<RichError> = Vec::new();
                match elem {
                    parse::Item::Use(use_decl) => {
                        let full_path = match get_full_path(&self.libraries, use_decl) {
                            Ok(path) => path,
                            Err(err) => {
                                handler.push(err.with_source(importer_source.clone()));
                                continue;
                            }
                        };
                        let source_full_path = SourceName::Real(Arc::from(full_path));
                        let ind = self.lookup[&source_full_path];

                        let use_targets = match use_decl.items() {
                            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
                            parse::UseItems::List(elems) => elems.as_slice(),
                        };

                        for target in use_targets {
                            if let Some(err) = ProjectGraph::process_use_item(
                                &mut resolutions,
                                file_id,
                                ind,
                                target,
                                use_decl,
                            ) {
                                errors.push(err)
                            }
                        }
                    }
                    parse::Item::TypeAlias(alias) => {
                        if let Some(err) = Self::register_def(
                            &mut items,
                            &mut resolutions,
                            file_id,
                            elem,
                            alias.name().clone().into(),
                            alias.visibility(),
                        ) {
                            errors.push(err)
                        }
                    }
                    parse::Item::Function(function) => {
                        if let Some(err) = Self::register_def(
                            &mut items,
                            &mut resolutions,
                            file_id,
                            elem,
                            function.name().clone().into(),
                            function.visibility(),
                        ) {
                            errors.push(err)
                        }
                    }
                    parse::Item::Module => {}
                }
                handler.update_with_source_enrichment(importer_source.clone(), errors);
            }
        }

        if handler.has_errors() {
            None
        } else {
            Some(Program {
                items: items.into(),
                paths: self.paths.clone(),
                resolutions: resolutions.into(),
                span: *self.modules[0].parsed_program.as_ref(),
            })
        }
    }

    pub fn resolve_complication_order(&self, handler: &mut ErrorCollector) -> Option<Program> {
        // TODO: @LesterEvSe, resolve errors more appropriately
        let mut order = self.c3_linearize().unwrap();
        order.reverse();
        self.build_program(&order, handler)
    }
}

fn merge(mut seqs: Vec<Vec<usize>>) -> Option<Vec<usize>> {
    let mut result = Vec::new();

    loop {
        seqs.retain(|s| !s.is_empty());
        if seqs.is_empty() {
            return Some(result);
        }

        let mut candidate = None;

        'outer: for seq in &seqs {
            let head = seq[0];

            if seqs.iter().all(|s| !s[1..].contains(&head)) {
                candidate = Some(head);
                break 'outer;
            }
        }

        let head = candidate?;

        result.push(head);

        for seq in &mut seqs {
            if seq.first() == Some(&head) {
                seq.remove(0);
            }
        }
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 1. Print the actual program code first
        for item in self.items.iter() {
            writeln!(f, "{item}")?;
        }

        // 2. Open the Resolution Table block
        writeln!(f, "\n/* --- RESOLUTION TABLE ---")?;

        // 3. Logic: Empty vs Populated
        if self.resolutions.is_empty() {
            writeln!(f, "             EMPTY")?;
        } else {
            for (file_id, scope) in self.resolutions.iter().enumerate() {
                if scope.is_empty() {
                    writeln!(f, "   File ID {}: (No resolutions)", file_id)?;
                    continue;
                }

                writeln!(f, "   File ID {}:", file_id)?;

                for (ident, resolution) in scope {
                    writeln!(f, "     {}: {:?}", ident, resolution.visibility)?;
                }
            }
        }

        // 4. Close the block (This runs for both empty and non-empty cases)
        writeln!(f, "*/")?;

        Ok(())
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TypeAlias(alias) => write!(f, "{alias}"),
            Self::Function(function) => write!(f, "{function}"),
            // The parse tree contains no information about the contents of modules.
            // We print a random empty module `mod witness {}` here
            // so that `from_string(to_string(x)) = x` holds for all trees `x`.
            Self::Module => write!(f, "mod witness {{}}"),
        }
    }
}

impl fmt::Display for TypeAlias {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "type {} = {};", self.name(), self.ty())
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn {} [file_id: {}] (", self.name(), self.file_id())?;
        for (i, param) in self.params().iter().enumerate() {
            if 0 < i {
                write!(f, ", ")?;
            }
            write!(f, "{param}")?;
        }
        write!(f, ")")?;
        if let Some(ty) = self.ret() {
            write!(f, " -> {ty}")?;
        }
        write!(f, " {}", self.body())
    }
}

impl AsRef<Span> for Program {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Function {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for TypeAlias {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Function {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <Self as crate::ArbitraryRec>::arbitrary_rec(u, 3)
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Function {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let file_id = u.int_in_range(0..=5)?;
        let name = FunctionName::arbitrary(u)?;
        let len = u.int_in_range(0..=3)?;
        let params = (0..len)
            .map(|_| parse::FunctionParam::arbitrary(u))
            .collect::<arbitrary::Result<Arc<[parse::FunctionParam]>>>()?;
        let ret = Option::<AliasedType>::arbitrary(u)?;
        let body =
            parse::Expression::arbitrary_rec(u, budget).map(parse::Expression::into_block)?;
        Ok(Self {
            file_id,
            name,
            params,
            ret,
            body,
            span: Span::DUMMY,
        })
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use std::fs::{self, File};
    use std::io::Write;
    use std::path::Path;
    use tempfile::TempDir;

    // --- Helper to setup environment ---
    // Creates a file with specific content in the temp directory
    pub(crate) fn create_simf_file(dir: &Path, rel_path: &str, content: &str) -> PathBuf {
        let full_path = dir.join(rel_path);

        // Ensure parent directories exist
        if let Some(parent) = full_path.parent() {
            fs::create_dir_all(parent).unwrap();
        }

        let mut file = File::create(&full_path).expect("Failed to create file");
        file.write_all(content.as_bytes())
            .expect("Failed to write content");
        full_path
    }

    // Helper to mock the initial root program parsing
    // (Assuming your parser works via a helper function)
    fn parse_root(path: &Path) -> (parse::Program, SourceFile) {
        // 1. Read file
        let content = std::fs::read_to_string(path).expect("Failed to read root file for parsing");

        // 2. Create SourceFile (needed for the new parser signature)
        // Note: We use the full path here; the logic inside `new` handles extension removal if needed
        let source = SourceFile::new(
            SourceName::Real(Arc::from(path)),
            Arc::from(content.clone()),
        );

        // 3. Create a temporary handler just for this parse
        let mut handler = ErrorCollector::new();

        // 4. Parse
        let program =
            parse::Program::parse_from_str_with_errors(&content, source.clone(), &mut handler);

        // 5. Check results
        assert!(
            !handler.has_errors(),
            "Test Setup Failed: Root file syntax error: {}",
            ErrorCollector::to_string(&handler)
        );

        (program.expect("Root parsing failed internally"), source)
    }

    /// Sets up a graph with "lib" mapped to "libs/lib".
    /// Files format: vec![("main.simf", "content"), ("libs/lib/A.simf", "content")]
    fn setup_graph(files: Vec<(&str, &str)>) -> (ProjectGraph, HashMap<String, usize>, TempDir) {
        let temp_dir = TempDir::new().unwrap();

        // 1. Create Files
        let mut root_path = None;
        for (name, content) in files {
            let path = create_simf_file(temp_dir.path(), name, content);
            if name == "main.simf" {
                root_path = Some(path);
            }
        }
        let root_p = root_path.expect("Tests must define 'main.simf'");

        // 2. Setup Libraries (Hardcoded "lib" -> "libs/lib" for simplicity in tests)
        let mut lib_map = HashMap::new();
        lib_map.insert("lib".to_string(), temp_dir.path().join("libs/lib"));

        // 3. Parse & Build
        let (root_program, source) = parse_root(&root_p);

        let mut handler = ErrorCollector::new();

        let graph = ProjectGraph::new(source, Arc::from(lib_map), &root_program, &mut handler)
            .expect(
                "setup_graph expects a valid graph construction. Use manual setup for error tests.",
            );

        // 4. Create Lookup (File Name -> ID) for easier asserting
        let mut file_ids = HashMap::new();
        for (source_name, id) in &graph.lookup {
            let simple_name = match source_name {
                SourceName::Real(path) => path.file_name().unwrap().to_string_lossy().to_string(),
                SourceName::Virtual(name) => name.to_string(),
            };
            file_ids.insert(simple_name, *id);
        }

        (graph, file_ids, temp_dir)
    }

    #[test]
    fn test_local_definitions_visibility() {
        // Scenario:
        // main.simf defines a private function and a public function.
        // Expected: Both should appear in the scope with correct visibility.

        let (graph, ids, _dir) = setup_graph(vec![(
            "main.simf",
            "fn private_fn() {} pub fn public_fn() {}",
        )]);

        let root_id = *ids.get("main").unwrap();
        let order = vec![root_id]; // Only one file

        let mut error_handler = ErrorCollector::new();
        let program = graph
            .build_program(&order, &mut error_handler)
            .expect("Failed to build program");
        let scope = &program.resolutions[root_id];

        // Check private function
        let private_res = scope
            .get(&Identifier::from("private_fn"))
            .expect("private_fn missing");
        assert_eq!(private_res.visibility, Visibility::Private);

        // Check public function
        let public_res = scope
            .get(&Identifier::from("public_fn"))
            .expect("public_fn missing");
        assert_eq!(public_res.visibility, Visibility::Public);
    }

    #[test]
    fn test_pub_use_propagation() {
        // Scenario: Re-exporting.
        // 1. A.simf defines `pub fn foo`.
        // 2. B.simf imports it and re-exports it via `pub use`.
        // 3. main.simf imports it from B.
        // Expected: B's scope must contain `foo` marked as Public.

        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub use lib::A::foo;"),
            ("main.simf", "use lib::B::foo;"),
        ]);

        let id_a = *ids.get("A").unwrap();
        let id_b = *ids.get("B").unwrap();
        let id_root = *ids.get("main").unwrap();

        // Manual topological order: A -> B -> Root
        let order = vec![id_a, id_b, id_root];

        let mut error_handler = ErrorCollector::new();
        let program = graph
            .build_program(&order, &mut error_handler)
            .expect("Failed to build program");

        // Check B's scope
        let scope_b = &program.resolutions[id_b];
        let foo_in_b = scope_b
            .get(&Identifier::from("foo"))
            .expect("foo missing in B");

        // This is the critical check: Did `pub use` make it Public in B?
        assert_eq!(
            foo_in_b.visibility,
            Visibility::Public,
            "B should re-export foo as Public"
        );

        // Check Root's scope
        let scope_root = &program.resolutions[id_root];
        let foo_in_root = scope_root
            .get(&Identifier::from("foo"))
            .expect("foo missing in Root");

        // Root imported it via `use` (not pub use), so it should be Private in Root
        assert_eq!(
            foo_in_root.visibility,
            Visibility::Private,
            "Root should have foo as Private"
        );
    }

    #[test]
    fn test_private_import_encapsulation_error() {
        // Scenario: Access violation.
        // 1. A.simf defines `pub fn foo`.
        // 2. B.simf imports it via `use` (Private import).
        // 3. main.simf tries to import `foo` from B.
        // Expected: Error, because B did not re-export foo.

        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "use lib::A::foo;"), // <--- Private binding!
            ("main.simf", "use lib::B::foo;"),       // <--- Should fail
        ]);

        let id_a = *ids.get("A").unwrap();
        let id_b = *ids.get("B").unwrap();
        let id_root = *ids.get("main").unwrap();

        // Order: A -> B -> Root
        let order = vec![id_a, id_b, id_root];

        let mut error_handler = ErrorCollector::new();
        let result = graph.build_program(&order, &mut error_handler);

        assert!(
            result.is_none(),
            "Build should fail when importing a private binding"
        );

        assert!(
            error_handler.has_errors(),
            "Error handler should contain errors"
        );

        let err_msg = ErrorCollector::to_string(&error_handler);
        assert!(
            err_msg.contains("private"),
            "Error message should mention 'private', but got: \n{}",
            err_msg
        );
    }

    #[test]
    fn test_simple_import() {
        // Setup:
        // main.simf -> "use lib::math;"
        // libs/lib/math.simf -> ""
        // Note: Changed "std" to "lib" to match setup_graph default config

        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::math::some_func;"),
            ("libs/lib/math.simf", ""),
        ]);

        assert_eq!(graph.modules.len(), 2, "Should have Root and Math module");

        // Check dependency: Root depends on Math
        let root_id = ids["main"];
        let math_id = ids["math"];

        assert!(
            graph.dependencies[&root_id].contains(&math_id),
            "Root (main.simf) should depend on Math (math.simf)"
        );
    }

    #[test]
    fn test_c3_simple_import() {
        // Setup similar to above
        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::math::some_func;"),
            ("libs/lib/math.simf", ""),
        ]);

        let order = graph.c3_linearize().expect("C3 failed");

        let root_id = ids["main"];
        let math_id = ids["math"];

        // Assuming linearization order: Dependent (Root) -> Dependency (Math)
        // Or vice-versa based on your specific C3 impl.
        // Based on your previous test `vec![0, 1]`, it seems like [Root, Math].
        assert_eq!(order, vec![root_id, math_id]);
    }

    #[test]
    fn test_diamond_dependency_deduplication() {
        // Setup:
        // root -> imports A, B
        // A -> imports Common
        // B -> imports Common
        // Expected: Common loaded ONLY ONCE (total 4 modules).

        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::foo; use lib::B::bar;"),
            ("libs/lib/A.simf", "use lib::Common::dummy1;"),
            ("libs/lib/B.simf", "use lib::Common::dummy2;"),
            ("libs/lib/Common.simf", ""),
        ]);

        // 1. Check strict deduplication (Unique modules count)
        assert_eq!(
            graph.modules.len(),
            4,
            "Should resolve exactly 4 unique modules (Main, A, B, Common)"
        );

        // 2. Verify Graph Topology via IDs
        let a_id = ids["A"];
        let b_id = ids["B"];
        let common_id = ids["Common"];

        // Check A -> Common
        assert!(
            graph.dependencies[&a_id].contains(&common_id),
            "A should depend on Common"
        );

        // Check B -> Common (Crucial: Must be the SAME common_id)
        assert!(
            graph.dependencies[&b_id].contains(&common_id),
            "B should depend on Common"
        );
    }

    #[test]
    fn test_c3_diamond_dependency_deduplication() {
        // Setup:
        // root (main) -> imports A, B
        // A -> imports Common
        // B -> imports Common
        // Expected: Common loaded ONLY ONCE.

        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::foo; use lib::B::bar;"),
            ("libs/lib/A.simf", "use lib::Common::dummy1;"),
            ("libs/lib/B.simf", "use lib::Common::dummy2;"),
            ("libs/lib/Common.simf", ""),
        ]);

        let order = graph.c3_linearize().expect("C3 failed");

        // Verify order using IDs from the helper map
        let main_id = ids["main"];
        let a_id = ids["A"];
        let b_id = ids["B"];
        let common_id = ids["Common"];

        // Common must be first (or early), Main last.
        // Exact topological sort might vary for A and B, but Common must be before them.
        assert_eq!(order, vec![main_id, a_id, b_id, common_id]); // Or [common, a, b, main]
    }

    #[test]
    fn test_cyclic_dependency_graph_structure() {
        // Setup: A <-> B cycle
        // main -> imports A
        // A -> imports B
        // B -> imports A

        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::entry;"),
            ("libs/lib/A.simf", "use lib::B::func;"),
            ("libs/lib/B.simf", "use lib::A::func;"),
        ]);

        let a_id = ids["A"];
        let b_id = ids["B"];

        // Check if graph correctly recorded the cycle
        assert!(
            graph.dependencies[&a_id].contains(&b_id),
            "A should depend on B"
        );
        assert!(
            graph.dependencies[&b_id].contains(&a_id),
            "B should depend on A"
        );
    }

    #[test]
    fn test_c3_detects_cycle() {
        // Uses the same logic as above but verifies linearization fails
        let (graph, _, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::entry;"),
            ("libs/lib/A.simf", "use lib::B::func;"),
            ("libs/lib/B.simf", "use lib::A::func;"),
        ]);

        let result = graph.c3_linearize();
        assert!(matches!(result, Err(C3Error::CycleDetected(_))));
    }

    #[test]
    fn test_ignores_unmapped_imports() {
        // Setup: root imports from "unknown", which is not in our lib_map
        let (graph, ids, _dir) = setup_graph(vec![("main.simf", "use unknown::library;")]);

        assert_eq!(graph.modules.len(), 1, "Should only contain root");
        assert!(graph.dependencies[&ids["main"]].is_empty());
    }

    #[test]
    fn test_missing_file_error() {
        // MANUAL SETUP REQUIRED
        // We cannot use `setup_graph` here because we expect `ProjectGraph::new` to fail/return None.

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "main.simf", "use lib::ghost::Phantom;");
        // We purposefully DO NOT create ghost.simf

        let mut lib_map = HashMap::new();
        lib_map.insert("lib".to_string(), temp_dir.path().join("libs/lib"));

        let (root_program, root_source) = parse_root(&root_path);
        let mut handler = ErrorCollector::new();

        let result =
            ProjectGraph::new(root_source, Arc::from(lib_map), &root_program, &mut handler);

        assert!(result.is_none(), "Graph construction should fail");
        assert!(handler.has_errors());

        let error_msg = ErrorCollector::to_string(&handler);
        assert!(
            error_msg.contains("File not found") || error_msg.contains("ghost.simf"),
            "Error message should mention 'ghost.simf' or 'File not found'. Got: {}",
            error_msg
        );
    }
}
