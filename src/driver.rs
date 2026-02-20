use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::{ErrorCollector, Span};
use crate::parse::{self, ParseFromStrWithErrors, Visibility};
use crate::str::{AliasName, FunctionName, Identifier};
use crate::types::AliasedType;
use crate::{get_full_path, impl_eq_hash, LibTable, SourceName};

/// Graph Node: One file = One module
#[derive(Debug, Clone)]
struct Module {
    /// Parsed AST (your `parse::Program`)
    /// Using Option to first create the node, then add the AST
    pub parsed_program: parse::Program,
}

/// The Dependency Graph itself
pub struct ProjectGraph {
    /// Arena Pattern: the data itself lies here. Vector guarantees data lives in one place.
    pub(self) modules: Vec<Module>,

    /// Fast lookup: Path -> ID
    /// Solves the duplicate problem (so as not to parse a.simf twice)
    //pub config: Arc<LibConfig>,
    pub libraries: Arc<LibTable>,
    pub lookup: HashMap<SourceName, usize>,
    pub paths: Arc<[SourceName]>,

    /// Adjacency list: Who depends on whom
    pub dependencies: HashMap<usize, Vec<usize>>,
}

// TODO: Consider to change BTreeMap to BTreeSet here
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
    pub fn from_parse(parsed: &parse::Program, root_path: SourceName) -> Result<Self, String> {
        let root_path = root_path.without_extension();

        let mut items: Vec<Item> = Vec::new();
        let mut resolutions: Vec<FileResolutions> = vec![BTreeMap::new()];

        let main_file_id = 0usize;
        let mut errors: Vec<String> = Vec::new();

        for item in parsed.items() {
            match item {
                parse::Item::Use(_) => {
                    errors.push("Unsuitable Use type".to_string());
                }
                parse::Item::TypeAlias(alias) => {
                    let res = ProjectGraph::register_def(
                        &mut items,
                        &mut resolutions,
                        main_file_id,
                        item,
                        alias.name().clone().into(),
                        &parse::Visibility::Public,
                    );

                    if let Err(e) = res {
                        errors.push(e);
                    }
                }
                parse::Item::Function(function) => {
                    let res = ProjectGraph::register_def(
                        &mut items,
                        &mut resolutions,
                        main_file_id,
                        item,
                        function.name().clone().into(),
                        &parse::Visibility::Public,
                    );

                    if let Err(e) = res {
                        errors.push(e);
                    }
                }
                parse::Item::Module => {}
            }
        }

        if !errors.is_empty() {
            return Err(errors.join("\n"));
        }

        Ok(Program {
            items: items.into(),
            paths: Arc::from([root_path]),
            resolutions: resolutions.into(),
            span: *parsed.as_ref(),
        })
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
    pub fn from_parse(parsed: &parse::Item, file_id: usize) -> Result<Self, String> {
        match parsed {
            parse::Item::TypeAlias(alias) => {
                let driver_alias = TypeAlias::from_parse(alias, file_id);
                Ok(Item::TypeAlias(driver_alias))
            }
            parse::Item::Function(func) => {
                let driver_func = Function::from_parse(func, file_id);
                Ok(Item::Function(driver_func))
            }
            parse::Item::Module => Ok(Item::Module),

            // Cannot convert Use to driver::Item
            parse::Item::Use(_) => Err("Unsuitable Use type".to_string()),
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
    file_id: usize, // NOTE: Maybe don't need
    name: AliasName,
    ty: AliasedType,
    span: Span,
}

impl TypeAlias {
    /// Converts a parser function to a driver function.
    ///
    /// We explicitly pass `file_id` here because the `parse::Function`
    /// doesn't know which file it came from.
    pub fn from_parse(parsed: &parse::TypeAlias, file_id: usize) -> Self {
        Self {
            file_id,
            name: parsed.name().clone(),
            ty: parsed.ty().clone(),
            span: *parsed.as_ref(),
        }
    }

    /// Access the visibility of the alias.
    pub fn file_id(&self) -> usize {
        self.file_id
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

impl_eq_hash!(TypeAlias; file_id, name, ty);

#[derive(Debug)]
pub enum C3Error {
    CycleDetected(Vec<usize>),
    InconsistentLinearization { module: usize },
}

fn parse_and_get_program(prog_file: &Path) -> Result<parse::Program, String> {
    let prog_text = std::fs::read_to_string(prog_file).map_err(|e| e.to_string())?;
    let file = prog_text.into();
    let mut error_handler = crate::error::ErrorCollector::new(Arc::clone(&file));

    if let Some(program) = parse::Program::parse_from_str_with_errors(&file, &mut error_handler) {
        Ok(program)
    } else {
        Err(ErrorCollector::to_string(&error_handler))?
    }
}

impl ProjectGraph {
    pub fn new(
        source_name: SourceName,
        libraries: Arc<LibTable>,
        root_program: &parse::Program,
    ) -> Result<Self, String> {
        let source_name = source_name.without_extension();
        let mut modules: Vec<Module> = vec![Module {
            parsed_program: root_program.clone(),
        }];
        let mut lookup: HashMap<SourceName, usize> = HashMap::new();
        let mut paths: Vec<SourceName> = vec![source_name.clone()];
        let mut dependencies: HashMap<usize, Vec<usize>> = HashMap::new();

        let root_id = 0;
        lookup.insert(source_name, root_id);
        dependencies.insert(root_id, Vec::new());

        // Implementation of the standard BFS algorithm with memoization and queue
        let mut queue = VecDeque::new();
        queue.push_back(root_id);

        while let Some(curr_id) = queue.pop_front() {
            let mut pending_imports: Vec<PathBuf> = Vec::new();
            let current_program = &modules[curr_id].parsed_program;

            for elem in current_program.items() {
                if let parse::Item::Use(use_decl) = elem {
                    if let Ok(path) = get_full_path(&libraries, use_decl) {
                        pending_imports.push(path);
                    }
                }
            }

            for path in pending_imports {
                let full_path = path.with_extension("simf");
                let source_path = SourceName::Real(path);

                if !full_path.is_file() {
                    return Err(format!("File in {:?}, does not exist", full_path));
                }

                if let Some(&existing_id) = lookup.get(&source_path) {
                    dependencies.entry(curr_id).or_default().push(existing_id);
                    continue;
                }

                let last_ind = modules.len();
                let program = parse_and_get_program(&full_path)?;

                modules.push(Module {
                    parsed_program: program,
                });
                lookup.insert(source_path.clone(), last_ind);
                paths.push(source_path.clone());
                dependencies.entry(curr_id).or_default().push(last_ind);

                queue.push_back(last_ind);
            }
        }

        Ok(Self {
            modules,
            libraries,
            lookup,
            paths: paths.into(),
            dependencies,
        })
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

    // TODO: @Sdoba16 to implement
    // fn build_ordering(&self) {}

    fn process_use_item(
        resolutions: &mut [FileResolutions],
        file_id: usize,
        ind: usize,
        elem: &Identifier,
        use_decl_visibility: Visibility,
    ) -> Result<(), String> {
        if matches!(
            resolutions[ind][elem].visibility,
            parse::Visibility::Private
        ) {
            return Err(format!(
                "Function {} is private and cannot be used.",
                elem.as_inner()
            ));
        }

        resolutions[file_id].insert(
            elem.clone(),
            Resolution {
                visibility: use_decl_visibility,
            },
        );

        Ok(())
    }

    fn register_def(
        items: &mut Vec<Item>,
        resolutions: &mut [FileResolutions],
        file_id: usize,
        item: &parse::Item,
        name: Identifier,
        vis: &parse::Visibility,
    ) -> Result<(), String> {
        items.push(Item::from_parse(item, file_id)?);
        resolutions[file_id].insert(
            name,
            Resolution {
                visibility: vis.clone(),
            },
        );
        Ok(())
    }

    // TODO: Change. Consider processing more than one error at a time
    fn build_program(&self, order: &Vec<usize>) -> Result<Program, String> {
        let mut items: Vec<Item> = Vec::new();
        let mut resolutions: Vec<FileResolutions> = vec![BTreeMap::new(); order.len()];

        for &file_id in order {
            let program_items = self.modules[file_id].parsed_program.items();

            for elem in program_items {
                match elem {
                    parse::Item::Use(use_decl) => {
                        let full_path = get_full_path(&self.libraries, use_decl)?;
                        let source_full_path = SourceName::Real(full_path);
                        let ind = self.lookup[&source_full_path];
                        let visibility = use_decl.visibility();

                        let use_targets = match use_decl.items() {
                            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
                            parse::UseItems::List(elems) => elems.as_slice(),
                        };

                        for target in use_targets {
                            ProjectGraph::process_use_item(
                                &mut resolutions,
                                file_id,
                                ind,
                                target,
                                visibility.clone(),
                            )?;
                        }
                    }
                    parse::Item::TypeAlias(alias) => {
                        Self::register_def(
                            &mut items,
                            &mut resolutions,
                            file_id,
                            elem,
                            alias.name().clone().into(),
                            alias.visibility(),
                        )?;
                    }
                    parse::Item::Function(function) => {
                        Self::register_def(
                            &mut items,
                            &mut resolutions,
                            file_id,
                            elem,
                            function.name().clone().into(),
                            function.visibility(),
                        )?;
                    }
                    parse::Item::Module => {}
                }
            }
        }

        Ok(Program {
            items: items.into(),
            paths: self.paths.clone(),
            resolutions: resolutions.into(),
            span: *self.modules[0].parsed_program.as_ref(),
        })
    }

    pub fn resolve_complication_order(&self) -> Result<Program, String> {
        // TODO: Resolve errors more appropriately
        let mut order = self.c3_linearize().unwrap();
        order.reverse();
        // self.build_ordering();
        self.build_program(&order)
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
        write!(
            f,
            "type {} [file_id: {}]  = {};",
            self.name(),
            self.file_id(),
            self.ty()
        )
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

    // ProjectGraph::new tests
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
    fn parse_root(path: &Path) -> parse::Program {
        parse_and_get_program(path).expect("Root parsing failed")
    }

    /// Initializes a graph environment for testing.
    /// Returns:
    /// 1. The constructed `ProjectGraph`.
    /// 2. A `HashMap` mapping filenames (e.g., "A.simf") to their `FileID` (usize).
    /// 3. The `TempDir` (to keep files alive during the test).
    fn setup_graph(files: Vec<(&str, &str)>) -> (ProjectGraph, HashMap<String, usize>, TempDir) {
        let temp_dir = TempDir::new().unwrap();
        let mut lib_map = HashMap::new();

        // Define the standard library path structure
        let lib_path = temp_dir.path().join("libs/lib");
        lib_map.insert("lib".to_string(), lib_path);

        let mut root_path = None;

        // Create all requested files
        for (name, content) in files {
            if name == "main.simf" {
                root_path = Some(create_simf_file(temp_dir.path(), name, content));
            } else {
                // Names should be passed like "libs/lib/A.simf"
                create_simf_file(temp_dir.path(), name, content);
            }
        }

        let root_p = root_path.expect("main.simf must be defined in file list");
        let root_program = parse_root(&root_p);

        let source_name = SourceName::Real(root_p);
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Failed to build graph");

        // Create a lookup map for tests: "A.simf" -> FileID
        let mut file_ids = HashMap::new();
        for (path, id) in &graph.lookup {
            let file_name = match path {
                SourceName::Real(path) => path.file_name().unwrap().to_string_lossy().to_string(),
                SourceName::Virtual(name) => name.clone(),
            };
            file_ids.insert(file_name, *id);
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

        let program = graph
            .build_program(&order)
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

        let program = graph
            .build_program(&order)
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

        let result = graph.build_program(&order);

        assert!(
            result.is_err(),
            "Build should fail when importing a private binding"
        );

        // Optional: Verify the error message contains relevant info
        // let err = result.err().unwrap();
        // assert!(err.to_string().to_lowercase().contains("private"));
    }

    /*
    #[test]
    fn test_renaming_with_use() {
        // Scenario: Renaming imports.
        // main.simf: use lib::A::foo as bar;
        // Expected: Scope should contain "bar", but not "foo".

        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf",       "use lib::A::foo;"),
        ]);

        let id_a = *ids.get("A.simf").unwrap();
        let id_root = *ids.get("main.simf").unwrap();
        let order = vec![id_a, id_root];

        let program = graph.build_program(&order).expect("Failed to build program");
        let scope = &program.resolutions[id_root];

        assert!(scope.get(&Identifier::from("foo")).is_none(), "Original name 'foo' should not be in scope");
        assert!(scope.get(&Identifier::from("bar")).is_some(), "Alias 'bar' should be in scope");
    }
    */

    #[test]
    fn test_simple_import() {
        // Setup:
        // root.simf -> "use std::math;"
        // libs/std/math.simf -> ""

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use std::math::some_func;");
        create_simf_file(temp_dir.path(), "libs/std/math.simf", "");

        // Setup Library Map
        let mut lib_map = HashMap::new();
        lib_map.insert("std".to_string(), temp_dir.path().join("libs/std"));

        // Parse Root
        let root_program = parse_root(&root_path);
        let source_name = SourceName::Real(root_path);

        // Run Logic
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Graph build failed");

        // Assertions
        assert_eq!(graph.modules.len(), 2, "Should have Root and Math module");
        assert!(
            graph.dependencies[&0].contains(&1),
            "Root should depend on Math"
        );
    }

    #[test]
    fn test_c3_simple_import() {
        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use std::math::some_func;");
        create_simf_file(temp_dir.path(), "libs/std/math.simf", "");

        let mut lib_map = HashMap::new();
        lib_map.insert("std".to_string(), temp_dir.path().join("libs/std"));

        let root_program = parse_root(&root_path);
        let source_name = SourceName::Real(root_path);
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Graph build failed");

        let order = graph.c3_linearize().expect("C3 failed");

        assert_eq!(order, vec![0, 1]);
    }

    #[test]
    fn test_diamond_dependency_deduplication() {
        // Setup:
        // root -> imports A, B
        // A -> imports Common
        // B -> imports Common
        // Expected: Common loaded ONLY ONCE.

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(
            temp_dir.path(),
            "root.simf",
            "use lib::A::foo; use lib::B::bar;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/lib/A.simf",
            "use lib::Common::dummy1;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/lib/B.simf",
            "use lib::Common::dummy2;",
        );
        create_simf_file(temp_dir.path(), "libs/lib/Common.simf", ""); // Empty leaf

        let mut lib_map = HashMap::new();
        lib_map.insert("lib".to_string(), temp_dir.path().join("libs/lib"));

        let root_program = parse_root(&root_path);
        let source_name = SourceName::Real(root_path);
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Graph build failed");

        // Assertions
        // Structure: Root(0), A(1), B(2), Common(3)
        assert_eq!(
            graph.modules.len(),
            4,
            "Should resolve exactly 4 unique modules"
        );

        // Check A -> Common
        let a_id = 1;
        let common_id = 3;
        assert!(graph.dependencies[&a_id].contains(&common_id));

        // Check B -> Common (Should point to SAME ID)
        let b_id = 2;
        assert!(graph.dependencies[&b_id].contains(&common_id));
    }

    #[test]
    fn test_c3_diamond_dependency_deduplication() {
        // Setup:
        // root -> imports A, B
        // A -> imports Common
        // B -> imports Common
        // Expected: Common loaded ONLY ONCE.

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(
            temp_dir.path(),
            "root.simf",
            "use lib::A::foo; use lib::B::bar;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/lib/A.simf",
            "use lib::Common::dummy1;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/lib/B.simf",
            "use lib::Common::dummy2;",
        );
        create_simf_file(temp_dir.path(), "libs/lib/Common.simf", ""); // Empty leaf

        let mut lib_map = HashMap::new();
        lib_map.insert("lib".to_string(), temp_dir.path().join("libs/lib"));

        let root_program = parse_root(&root_path);
        let source_name = SourceName::Real(root_path);
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Graph build failed");

        let order = graph.c3_linearize().expect("C3 failed");

        assert_eq!(order, vec![0, 1, 2, 3],);
    }

    #[test]
    fn test_cyclic_dependency() {
        // Setup:
        // A -> imports B
        // B -> imports A
        // Expected: Should finish without infinite loop

        let temp_dir = TempDir::new().unwrap();
        let a_path = create_simf_file(
            temp_dir.path(),
            "libs/test/A.simf",
            "use test::B::some_test;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/test/B.simf",
            "use test::A::another_test;",
        );

        let mut lib_map = HashMap::new();
        lib_map.insert("test".to_string(), temp_dir.path().join("libs/test"));

        let root_program = parse_root(&a_path);
        let source_name = SourceName::Real(a_path);
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Graph build failed");

        assert_eq!(graph.modules.len(), 2, "Should only have A and B");

        // A depends on B
        assert!(graph.dependencies[&0].contains(&1));
        // B depends on A (Circular)
        assert!(graph.dependencies[&1].contains(&0));
    }

    #[test]
    fn test_c3_cyclic_dependency() {
        // Setup:
        // A -> imports B
        // B -> imports A
        // Expected: Should finish without infinite loop

        let temp_dir = TempDir::new().unwrap();
        let a_path = create_simf_file(
            temp_dir.path(),
            "libs/test/A.simf",
            "use test::B::some_test;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/test/B.simf",
            "use test::A::another_test;",
        );

        let mut lib_map = HashMap::new();
        lib_map.insert("test".to_string(), temp_dir.path().join("libs/test"));

        let root_program = parse_root(&a_path);
        let source_name = SourceName::Real(a_path);
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Graph build failed");

        let order = graph.c3_linearize().unwrap_err();
        matches!(order, C3Error::CycleDetected(_));
    }

    #[test]
    fn test_missing_file_error() {
        // Setup:
        // root -> imports missing_lib

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use std::ghost;");
        // We do NOT create ghost.simf

        let mut lib_map = HashMap::new();
        lib_map.insert("std".to_string(), temp_dir.path().join("libs/std"));

        let root_program = parse_root(&root_path);
        let source_name = SourceName::Real(root_path);
        let result = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program);

        assert!(result.is_err(), "Should fail for missing file");
        let err_msg = result.err().unwrap();
        assert!(
            err_msg.contains("does not exist"),
            "Error message should mention missing file"
        );
    }

    #[test]
    fn test_ignores_unmapped_imports() {
        // Setup:
        // root -> "use unknown::library;"
        // "unknown" is NOT in library_map.
        // Expected: It should simply skip this import (based on `if let Ok(path)` logic)

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use unknown::library;");

        let lib_map = HashMap::new(); // Empty map

        let root_program = parse_root(&root_path);
        let source_name = SourceName::Real(root_path);
        let graph = ProjectGraph::new(source_name, Arc::from(lib_map), &root_program)
            .expect("Should succeed but ignore import");

        assert_eq!(graph.modules.len(), 1, "Should only contain root");
        assert!(
            graph.dependencies[&0].is_empty(),
            "Root should have no resolved dependencies"
        );
    }
}
