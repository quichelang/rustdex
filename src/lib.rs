//! # Rustdex
//!
//! A compact, queryable index of Rust standard library trait implementations.
//!
//! Rustdex reads `rustdoc --output-format json` output and extracts trait
//! implementation data into a small binary index. This is useful for compilers,
//! transpilers, and code generators that need to know which types implement
//! which traits without parsing the entire standard library.
//!
//! ## Quick Start
//!
//! ```rust,no_run
//! fn main() -> Result<(), String> {
//!     use rustdex::{StdIndex, IndexBuilder};
//!
//!     // Build from rustdoc JSON
//!     let index = IndexBuilder::from_sysroot()?.build()?;
//!
//!     // Query: does HashMap implement FromIterator?
//!     let impls = index.find_impls_for("HashMap");
//!     for imp in &impls {
//!         println!("{} implements {}", imp.for_type, imp.trait_path);
//!     }
//!
//!     // Save as bincode (default) to sysroot
//!     index.save_to_sysroot()?;
//!     Ok(())
//! }
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

// ─────────────────────────────────────────────────────────────────────────
// Index data model
// ─────────────────────────────────────────────────────────────────────────

/// A compact index of trait implementations from a crate (std or otherwise).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CrateIndex {
    /// Rust compiler version this index was generated from (e.g. "1.85.0").
    pub rust_version: String,

    /// Timestamp when the index was generated.
    pub generated_at: String,

    /// rustdoc JSON format version used.
    pub format_version: u32,

    /// All trait implementations extracted from the crate(s).
    pub impls: Vec<TraitImpl>,
    #[serde(default)]
    pub functions: Vec<FunctionRecord>,
}

/// Backward compatibility alias.
pub type StdIndex = CrateIndex;

// ... (existing structures: TraitImpl, ReceiverMode, ParamSig, MethodSig) ...

impl CrateIndex {
    // ... (existing query methods: find_impls_for, find_implementors, implements, method_signature, has_method, stats) ...

    // ─────────────────────────────────────────────────────────────────────────
    // Persistence
    // ─────────────────────────────────────────────────────────────────────────

    /// Save the index as bincode to a file.
    pub fn save(&self, path: &Path) -> Result<(), String> {
        let data = bincode::serialize(self).map_err(|e| format!("bincode error: {e}"))?;
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        std::fs::write(path, &data).map_err(|e| format!("write error: {e}"))?;
        Ok(())
    }

    /// Load the index from a bincode file.
    pub fn load(path: &Path) -> Result<Self, String> {
        let data = std::fs::read(path).map_err(|e| format!("read error: {e}"))?;
        bincode::deserialize(&data).map_err(|e| format!("bincode error: {e}"))
    }

    /// Save to the default sysroot location.
    pub fn save_to_sysroot(&self) -> Result<PathBuf, String> {
        let dir = sysroot_json_dir()?;
        let path = dir.join(format!("rustdex_{}.bin", self.rust_version));
        self.save(&path)?;
        Ok(path)
    }

    /// Load from the default sysroot location for the current Rust version.
    pub fn load_from_sysroot() -> Result<Self, String> {
        let version = rust_version()?;
        let dir = sysroot_json_dir()?;
        let path = dir.join(format!("rustdex_{version}.bin"));
        if path.exists() {
            Self::load(&path)
        } else {
            Err(format!(
                "No index found at {}. Run `rustdex build` first.",
                path.display()
            ))
        }
    }

    /// Export as JSON string. Always available since serde_json is a required
    /// dependency (used for parsing rustdoc input).
    pub fn to_json(&self) -> Result<String, String> {
        serde_json::to_string_pretty(self).map_err(|e| format!("json error: {e}"))
    }
}

// ... (IndexStats struct) ...

// ─────────────────────────────────────────────────────────────────────────
// Index builder (parses rustdoc JSON)
// ─────────────────────────────────────────────────────────────────────────

/// Builder that parses rustdoc JSON and produces a `CrateIndex`.
pub struct IndexBuilder {
    json_paths: Vec<PathBuf>,
}

impl IndexBuilder {
    /// Create a builder from an explicit path to a rustdoc JSON file.
    pub fn from_path(path: impl Into<PathBuf>) -> Self {
        Self {
            json_paths: vec![path.into()],
        }
    }

    /// Create a builder from multiple rustdoc JSON files.
    pub fn from_paths(paths: Vec<PathBuf>) -> Self {
        Self { json_paths: paths }
    }

    /// Create a builder that reads `std.json`, `core.json`, and `alloc.json`
    /// from the current toolchain's sysroot for complete coverage.
    ///
    /// Vec, String, Box, etc. have their trait impls in `alloc.json`.
    /// Primitive types (i32, bool, etc.) have theirs in `core.json`.
    pub fn from_sysroot() -> Result<Self, String> {
        ensure_rust_docs_json_installed()?;

        let dir = sysroot_json_dir()?;
        let mut paths = Vec::new();

        for name in ["std.json", "core.json", "alloc.json"] {
            let path = dir.join(name);
            if path.exists() {
                paths.push(path);
            }
        }

        if paths.is_empty() {
            return Err(format!(
                "No rustdoc JSON found at {}. Install with: rustup component add rust-docs-json",
                dir.display()
            ));
        }

        Ok(Self { json_paths: paths })
    }

    /// Parse all rustdoc JSON files and build a merged index.
    pub fn build(&self) -> Result<CrateIndex, String> {
        let version = rust_version()?;
        let now = chrono_lite_now();
        let mut all_impls = Vec::new();
        let mut all_functions = Vec::new();
        let mut format_version = 0u32;

        for path in &self.json_paths {
            let (fv, mut impls, mut functions) = Self::build_one(path)?;
            format_version = fv;
            all_impls.append(&mut impls);
            all_functions.append(&mut functions);
        }

        // Merge impls with the same (trait_name, for_type) across crates.
        let mut groups: HashMap<(String, String), TraitImpl> = HashMap::new();
        for imp in all_impls {
            let key = (imp.trait_name.clone(), imp.for_type.clone());
            groups
                .entry(key)
                .and_modify(|existing| {
                    for method in &imp.methods {
                        if !existing.methods.iter().any(|m| m.name == method.name) {
                            existing.methods.push(method.clone());
                        }
                    }
                    for at in &imp.associated_types {
                        if !existing.associated_types.iter().any(|(n, _)| n == &at.0) {
                            existing.associated_types.push(at.clone());
                        }
                    }
                })
                .or_insert(imp);
        }
        let mut all_impls: Vec<TraitImpl> = groups.into_values().collect();
        all_impls.sort_by(|a, b| {
            a.trait_name
                .cmp(&b.trait_name)
                .then(a.for_type.cmp(&b.for_type))
        });

        // ── Synthetic [T] inherent methods ───────────────────────────────
        // rustdoc JSON doesn't include item definitions for primitive slice
        // inherent impls (IDs exist but point to missing entries). Inject a
        // hardcoded table until rustdoc fixes this upstream.
        all_impls.push(synthetic_slice_impl());

        // Dedup functions by path
        let mut func_map: HashMap<String, FunctionRecord> = HashMap::new();
        for func in all_functions {
            func_map.entry(func.path.clone()).or_insert(func);
        }
        let mut unique_functions: Vec<FunctionRecord> = func_map.into_values().collect();
        unique_functions.sort_by(|a, b| a.path.cmp(&b.path));

        Ok(CrateIndex {
            rust_version: version,
            generated_at: now,
            format_version,
            impls: all_impls,
            functions: unique_functions,
        })
    }

    /// Parse a single rustdoc JSON file and extract impls (both trait and inherent) and functions.
    fn build_one(
        path: &std::path::Path,
    ) -> Result<(u32, Vec<TraitImpl>, Vec<FunctionRecord>), String> {
        let contents =
            std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;

        let krate: rustdoc_types::Crate = serde_json::from_str(&contents)
            .map_err(|e| format!("parse {}: {e}", path.display()))?;

        // Build path lookup: id → full path string
        let path_lookup: HashMap<rustdoc_types::Id, String> = krate
            .paths
            .iter()
            .map(|(id, summary)| (id.clone(), summary.path.join("::")))
            .collect();

        let mut impls = Vec::new();
        let mut functions = Vec::new();

        for (_id, item) in &krate.index {
            match &item.inner {
                rustdoc_types::ItemEnum::Impl(impl_item) => {
                    // Extract trait info (empty for inherent impls)
                    let (trait_path, trait_name) = match &impl_item.trait_ {
                        Some(t) => {
                            let tp = path_lookup
                                .get(&t.id)
                                .cloned()
                                .unwrap_or_else(|| t.path.clone());
                            let tn = short_path(&t.path);
                            (tp, tn)
                        }
                        None => (String::new(), String::new()),
                    };

                    let for_type = format_type(&impl_item.for_, &path_lookup);

                    let type_params: Vec<String> = impl_item
                        .generics
                        .params
                        .iter()
                        .map(|p| format_generic_param(p))
                        .collect();

                    let where_predicates: Vec<String> = impl_item
                        .generics
                        .where_predicates
                        .iter()
                        .map(|wp| format!("{wp:?}"))
                        .collect();

                    let methods: Vec<MethodSig> = impl_item
                        .items
                        .iter()
                        .filter_map(|item_id| {
                            let method_item = krate.index.get(item_id)?;
                            let func = match &method_item.inner {
                                rustdoc_types::ItemEnum::Function(f) => f,
                                _ => return None,
                            };
                            let name = method_item.name.clone()?;
                            Some(extract_method_sig(&name, func, &path_lookup))
                        })
                        .collect();

                    if methods.is_empty() {
                        continue;
                    }

                    impls.push(TraitImpl {
                        trait_path,
                        trait_name,
                        for_type,
                        type_params,
                        where_predicates,
                        associated_types: vec![],
                        methods,
                    });
                }
                rustdoc_types::ItemEnum::Function(func) => {
                    if let Some(name) = &item.name {
                        // Check visibility - only index public functions
                        if item.visibility == rustdoc_types::Visibility::Public {
                            let path = path_lookup
                                .get(&item.id)
                                .cloned()
                                .unwrap_or_else(|| name.clone());

                            let sig = extract_method_sig(name, func, &path_lookup);
                            functions.push(FunctionRecord {
                                path,
                                name: name.clone(),
                                sig,
                            });
                        }
                    }
                }
                _ => {}
            }
        }

        Ok((krate.format_version, impls, functions))
    }
}

/// A trait implementation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    /// Full trait path (e.g. "core::iter::traits::collect::FromIterator").
    /// Empty string for inherent impls (non-trait).
    pub trait_path: String,

    /// Short trait name (e.g. "FromIterator").
    /// Empty string for inherent impls.
    pub trait_name: String,

    /// The type that implements the trait (e.g. "HashMap<K, V>").
    pub for_type: String,

    /// Generic type parameters with bounds (e.g. ["K: Eq + Hash", "V"]).
    pub type_params: Vec<String>,

    /// Where clause predicates.
    pub where_predicates: Vec<String>,

    /// Associated types (name → type string).
    pub associated_types: Vec<(String, String)>,

    /// Method signatures provided by this impl.
    pub methods: Vec<MethodSig>,
}

/// A top-level function record.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionRecord {
    pub path: String, // e.g. "host::scan_dir"
    pub name: String, // "scan_dir"
    pub sig: MethodSig,
}

/// Receiver mode for a method.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverMode {
    /// No receiver (associated function / static method).
    None,
    /// `&self`
    Ref,
    /// `&mut self`
    RefMut,
    /// `self` (by value / owned)
    Owned,
}

/// A parameter in a method signature.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ParamSig {
    /// Parameter name.
    pub name: String,
    /// Formatted type string.
    pub ty: String,
    /// Whether the param is a reference (`&T` or `&mut T`).
    pub is_ref: bool,
    /// Whether the param is a mutable reference (`&mut T`).
    pub is_mut_ref: bool,
}

/// A method signature extracted from rustdoc JSON.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MethodSig {
    /// Method name.
    pub name: String,
    /// Receiver mode (`&self`, `&mut self`, `self`, or none).
    pub receiver: ReceiverMode,
    /// Parameters (excluding self).
    pub params: Vec<ParamSig>,
    /// Formatted return type string ("()" for unit).
    pub return_type: String,
}

impl MethodSig {
    /// Create a minimal `MethodSig` with just a name (defaults to `&self`, no params, `()` return).
    pub fn simple(name: &str) -> Self {
        MethodSig {
            name: name.to_string(),
            receiver: ReceiverMode::Ref,
            params: Vec::new(),
            return_type: "()".to_string(),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Index querying
// ─────────────────────────────────────────────────────────────────────────

impl CrateIndex {
    /// Find all trait impls for a given type name (substring match on `for_type`).
    pub fn find_impls_for(&self, type_name: &str) -> Vec<&TraitImpl> {
        self.impls
            .iter()
            .filter(|imp| imp.for_type.contains(type_name))
            .collect()
    }

    /// Look up a top-level function signature by path.
    ///
    /// e.g. `lookup_function("host::scan_dir")`
    pub fn lookup_function(&self, path: &str) -> Option<&MethodSig> {
        self.functions
            .iter()
            .find(|f| f.path == path)
            .map(|f| &f.sig)
    }

    /// Find all types implementing a given trait (substring match on `trait_name`).
    pub fn find_implementors(&self, trait_name: &str) -> Vec<&TraitImpl> {
        self.impls
            .iter()
            .filter(|imp| imp.trait_name == trait_name || imp.trait_path.contains(trait_name))
            .collect()
    }

    /// Check if a specific type implements a specific trait.
    pub fn implements(&self, type_name: &str, trait_name: &str) -> bool {
        self.impls.iter().any(|imp| {
            imp.for_type.contains(type_name)
                && (imp.trait_name == trait_name || imp.trait_path.contains(trait_name))
        })
    }

    /// Look up the signature of a method on a type.
    ///
    /// Searches all impls (both inherent and trait) for a method with the
    /// given name on a type whose `for_type` contains `type_name`.
    /// Returns the first match found.
    pub fn method_signature(&self, type_name: &str, method_name: &str) -> Option<&MethodSig> {
        for imp in &self.impls {
            if !imp.for_type.contains(type_name) {
                continue;
            }
            for method in &imp.methods {
                if method.name == method_name {
                    return Some(method);
                }
            }
        }
        None
    }

    /// Check if a type has a method with the given name (across all impls).
    pub fn has_method(&self, type_name: &str, method_name: &str) -> bool {
        self.method_signature(type_name, method_name).is_some()
    }

    /// Get summary statistics.
    pub fn stats(&self) -> IndexStats {
        let mut traits: HashMap<String, usize> = HashMap::new();
        let mut types: HashMap<String, usize> = HashMap::new();
        for imp in &self.impls {
            *traits.entry(imp.trait_name.clone()).or_default() += 1;
            *types.entry(imp.for_type.clone()).or_default() += 1;
        }
        IndexStats {
            total_impls: self.impls.len(),
            unique_traits: traits.len(),
            unique_types: types.len(),
            top_traits: {
                let mut v: Vec<_> = traits.into_iter().collect();
                v.sort_by(|a, b| b.1.cmp(&a.1));
                v.truncate(20);
                v
            },
        }
    }
}

/// Summary statistics for an index.
#[derive(Debug)]
pub struct IndexStats {
    pub total_impls: usize,
    pub unique_traits: usize,
    pub unique_types: usize,
    pub top_traits: Vec<(String, usize)>,
}

// ─────────────────────────────────────────────────────────────────────────
// Index builder (parses rustdoc JSON)
// ─────────────────────────────────────────────────────────────────────────

/// Extract a `MethodSig` from a rustdoc `Function` item.
fn extract_method_sig(
    name: &str,
    func: &rustdoc_types::Function,
    path_lookup: &HashMap<rustdoc_types::Id, String>,
) -> MethodSig {
    let mut receiver = ReceiverMode::None;
    let mut params = Vec::new();

    for (i, (param_name, ty)) in func.sig.inputs.iter().enumerate() {
        if i == 0 && param_name == "self" {
            receiver = match ty {
                rustdoc_types::Type::BorrowedRef { is_mutable, .. } => {
                    if *is_mutable {
                        ReceiverMode::RefMut
                    } else {
                        ReceiverMode::Ref
                    }
                }
                _ => ReceiverMode::Owned,
            };
            continue;
        }

        let (is_ref, is_mut_ref) = match ty {
            rustdoc_types::Type::BorrowedRef { is_mutable, .. } => (true, *is_mutable),
            _ => (false, false),
        };

        params.push(ParamSig {
            name: param_name.clone(),
            ty: format_type(ty, path_lookup),
            is_ref,
            is_mut_ref,
        });
    }

    let return_type = match &func.sig.output {
        Some(ty) => format_type(ty, path_lookup),
        None => "()".to_string(),
    };

    MethodSig {
        name: name.to_string(),
        receiver,
        params,
        return_type,
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Type formatting helpers
// ─────────────────────────────────────────────────────────────────────────

fn format_type(ty: &rustdoc_types::Type, paths: &HashMap<rustdoc_types::Id, String>) -> String {
    match ty {
        rustdoc_types::Type::ResolvedPath(path) => {
            let base = paths
                .get(&path.id)
                .map(|p| short_path(p))
                .unwrap_or_else(|| short_path(&path.path));

            if let Some(args) = &path.args {
                match args.as_ref() {
                    rustdoc_types::GenericArgs::AngleBracketed { args, .. } => {
                        if args.is_empty() {
                            base
                        } else {
                            let formatted: Vec<String> = args
                                .iter()
                                .filter_map(|arg| match arg {
                                    rustdoc_types::GenericArg::Type(t) => {
                                        Some(format_type(t, paths))
                                    }
                                    rustdoc_types::GenericArg::Lifetime(l) => Some(l.clone()),
                                    rustdoc_types::GenericArg::Const(c) => Some(format!("{:?}", c)),
                                    _ => None,
                                })
                                .collect();
                            format!("{base}<{}>", formatted.join(", "))
                        }
                    }
                    rustdoc_types::GenericArgs::Parenthesized { inputs, output } => {
                        let ins: Vec<String> =
                            inputs.iter().map(|t| format_type(t, paths)).collect();
                        match output {
                            Some(ret) => {
                                format!("{base}({}) -> {}", ins.join(", "), format_type(ret, paths))
                            }
                            None => format!("{base}({})", ins.join(", ")),
                        }
                    }
                    _ => base,
                }
            } else {
                base
            }
        }
        rustdoc_types::Type::Primitive(name) => name.clone(),
        rustdoc_types::Type::Tuple(types) => {
            let inner: Vec<String> = types.iter().map(|t| format_type(t, paths)).collect();
            format!("({})", inner.join(", "))
        }
        rustdoc_types::Type::Slice(inner) => format!("[{}]", format_type(inner, paths)),
        rustdoc_types::Type::Array { type_, len } => {
            format!("[{}; {}]", format_type(type_, paths), len)
        }
        rustdoc_types::Type::RawPointer { is_mutable, type_ } => {
            let prefix = if *is_mutable { "*mut" } else { "*const" };
            format!("{prefix} {}", format_type(type_, paths))
        }
        rustdoc_types::Type::BorrowedRef {
            lifetime,
            is_mutable,
            type_,
        } => {
            let lt = lifetime
                .as_ref()
                .map(|l| format!("{l} "))
                .unwrap_or_default();
            let mutability = if *is_mutable { "mut " } else { "" };
            format!("&{lt}{mutability}{}", format_type(type_, paths))
        }
        rustdoc_types::Type::Generic(name) => name.clone(),
        rustdoc_types::Type::QualifiedPath {
            name, self_type, ..
        } => {
            format!("<{}>::{}", format_type(self_type, paths), name)
        }
        _ => format!("{ty:?}"),
    }
}

/// Shorten a full path like "std::collections::hash_map::HashMap" → "HashMap"
fn short_path(path: &str) -> String {
    path.rsplit("::").next().unwrap_or(path).to_string()
}

fn format_generic_param(param: &rustdoc_types::GenericParamDef) -> String {
    match &param.kind {
        rustdoc_types::GenericParamDefKind::Type {
            bounds, default, ..
        } => {
            let mut s = param.name.clone();
            if !bounds.is_empty() {
                let bound_strs: Vec<String> = bounds
                    .iter()
                    .filter_map(|b| match b {
                        rustdoc_types::GenericBound::TraitBound { trait_, .. } => {
                            Some(short_path(&trait_.path))
                        }
                        _ => None,
                    })
                    .collect();
                if !bound_strs.is_empty() {
                    s = format!("{s}: {}", bound_strs.join(" + "));
                }
            }
            if let Some(def) = default {
                s = format!("{s} = {def:?}");
            }
            s
        }
        rustdoc_types::GenericParamDefKind::Lifetime { .. } => format!("'{}", param.name),
        rustdoc_types::GenericParamDefKind::Const { type_, .. } => {
            format!("const {}: {:?}", param.name, type_)
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Synthetic primitive slice methods
// ─────────────────────────────────────────────────────────────────────────

/// Generate a synthetic inherent impl for `[T]` containing common slice
/// methods. rustdoc JSON doesn't include definitions for primitive slice
/// inherent impls (the item IDs exist but point to missing entries).
fn synthetic_slice_impl() -> TraitImpl {
    let mut methods = Vec::new();

    // Helper to build a simple MethodSig
    let method = |name: &str, recv: ReceiverMode, params: Vec<ParamSig>, ret: &str| -> MethodSig {
        MethodSig {
            name: name.to_string(),
            receiver: recv,
            params,
            return_type: ret.to_string(),
        }
    };

    let param = |name: &str, ty: &str, is_ref: bool, is_mut_ref: bool| -> ParamSig {
        ParamSig {
            name: name.to_string(),
            ty: ty.to_string(),
            is_ref,
            is_mut_ref,
        }
    };

    // ── &self methods (read-only) ─────────────────────────────────────
    methods.push(method("len", ReceiverMode::Ref, vec![], "usize"));
    methods.push(method("is_empty", ReceiverMode::Ref, vec![], "bool"));
    methods.push(method("first", ReceiverMode::Ref, vec![], "Option<&T>"));
    methods.push(method("last", ReceiverMode::Ref, vec![], "Option<&T>"));
    methods.push(method(
        "get",
        ReceiverMode::Ref,
        vec![param("index", "usize", false, false)],
        "Option<&T>",
    ));
    methods.push(method(
        "contains",
        ReceiverMode::Ref,
        vec![param("x", "&T", true, false)],
        "bool",
    ));
    methods.push(method("iter", ReceiverMode::Ref, vec![], "Iter<T>"));
    methods.push(method(
        "windows",
        ReceiverMode::Ref,
        vec![param("size", "usize", false, false)],
        "Windows<T>",
    ));
    methods.push(method(
        "chunks",
        ReceiverMode::Ref,
        vec![param("chunk_size", "usize", false, false)],
        "Chunks<T>",
    ));
    methods.push(method(
        "split_at",
        ReceiverMode::Ref,
        vec![param("mid", "usize", false, false)],
        "(&[T], &[T])",
    ));
    methods.push(method(
        "binary_search",
        ReceiverMode::Ref,
        vec![param("x", "&T", true, false)],
        "Result<usize, usize>",
    ));
    methods.push(method(
        "starts_with",
        ReceiverMode::Ref,
        vec![param("needle", "&[T]", true, false)],
        "bool",
    ));
    methods.push(method(
        "ends_with",
        ReceiverMode::Ref,
        vec![param("needle", "&[T]", true, false)],
        "bool",
    ));
    methods.push(method("to_vec", ReceiverMode::Ref, vec![], "Vec<T>"));
    methods.push(method(
        "repeat",
        ReceiverMode::Ref,
        vec![param("n", "usize", false, false)],
        "Vec<T>",
    ));
    methods.push(method(
        "join",
        ReceiverMode::Ref,
        vec![param("sep", "&T", true, false)],
        "Vec<T>",
    ));

    // ── &mut self methods (mutating) ──────────────────────────────────
    methods.push(method("sort", ReceiverMode::RefMut, vec![], "()"));
    methods.push(method("sort_unstable", ReceiverMode::RefMut, vec![], "()"));
    methods.push(method(
        "sort_by",
        ReceiverMode::RefMut,
        vec![param("compare", "F", false, false)],
        "()",
    ));
    methods.push(method(
        "sort_unstable_by",
        ReceiverMode::RefMut,
        vec![param("compare", "F", false, false)],
        "()",
    ));
    methods.push(method(
        "sort_by_key",
        ReceiverMode::RefMut,
        vec![param("f", "F", false, false)],
        "()",
    ));
    methods.push(method("reverse", ReceiverMode::RefMut, vec![], "()"));
    methods.push(method(
        "swap",
        ReceiverMode::RefMut,
        vec![
            param("a", "usize", false, false),
            param("b", "usize", false, false),
        ],
        "()",
    ));
    methods.push(method(
        "rotate_left",
        ReceiverMode::RefMut,
        vec![param("mid", "usize", false, false)],
        "()",
    ));
    methods.push(method(
        "rotate_right",
        ReceiverMode::RefMut,
        vec![param("k", "usize", false, false)],
        "()",
    ));
    methods.push(method(
        "fill",
        ReceiverMode::RefMut,
        vec![param("value", "T", false, false)],
        "()",
    ));
    methods.push(method(
        "iter_mut",
        ReceiverMode::RefMut,
        vec![],
        "IterMut<T>",
    ));
    methods.push(method(
        "copy_from_slice",
        ReceiverMode::RefMut,
        vec![param("src", "&[T]", true, false)],
        "()",
    ));
    methods.push(method(
        "retain",
        ReceiverMode::RefMut,
        vec![param("f", "F", false, false)],
        "()",
    ));

    TraitImpl {
        trait_path: String::new(), // inherent impl
        trait_name: String::new(),
        for_type: "[T]".to_string(),
        type_params: vec!["T".to_string()],
        where_predicates: vec![],
        associated_types: vec![],
        methods,
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Utility functions
// ─────────────────────────────────────────────────────────────────────────

/// Get the active Rust compiler version string.
pub fn rust_version() -> Result<String, String> {
    let output = std::process::Command::new("rustc")
        .arg("--version")
        .output()
        .map_err(|e| format!("Failed to run rustc: {e}"))?;
    let version_str = String::from_utf8_lossy(&output.stdout);
    // Parse "rustc 1.85.0-nightly (abc123 2024-12-01)" → "1.85.0-nightly"
    let version = version_str
        .split_whitespace()
        .nth(1)
        .unwrap_or("unknown")
        .to_string();
    Ok(version)
}

/// Get the rustdoc JSON directory in the current sysroot.
pub fn sysroot_json_dir() -> Result<PathBuf, String> {
    let output = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .map_err(|e| format!("Failed to run rustc: {e}"))?;
    let sysroot = String::from_utf8_lossy(&output.stdout).trim().to_string();
    Ok(PathBuf::from(sysroot).join("share/doc/rust/json"))
}

/// Simple ISO 8601 timestamp without chrono dependency.
fn chrono_lite_now() -> String {
    let output = std::process::Command::new("date")
        .arg("-u")
        .arg("+%Y-%m-%dT%H:%M:%SZ")
        .output()
        .ok();
    output
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Ensure the `rust-docs-json` component is installed for the current toolchain.
///
/// This runs `rustup component add rust-docs-json` if the component is missing.
/// It detects the active toolchain via `rustup show`.
pub fn ensure_rust_docs_json_installed() -> Result<(), String> {
    // Check if we even have rustup
    if std::process::Command::new("rustup")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_err()
    {
        // No rustup, assume user knows what they're doing or we can't help
        return Ok(());
    }

    // Check if component is listed in `rustup component list --installed`
    let output = std::process::Command::new("rustup")
        .arg("component")
        .arg("list")
        .arg("--installed")
        .output()
        .map_err(|e| format!("Failed to run rustup component list: {e}"))?;

    let installed = String::from_utf8_lossy(&output.stdout);
    if installed.contains("rust-docs-json") {
        return Ok(());
    }

    // Attempt to install
    let install_output = std::process::Command::new("rustup")
        .arg("component")
        .arg("add")
        .arg("rust-docs-json")
        .output()
        .map_err(|e| format!("Failed to run rustup component add: {e}"))?;

    if !install_output.status.success() {
        return Err(format!(
            "Failed to install rust-docs-json component:\n{}",
            String::from_utf8_lossy(&install_output.stderr)
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // ─── Helpers ─────────────────────────────────────────────────────

    /// Build a minimal StdIndex for unit testing without parsing real JSON.
    fn sample_index() -> StdIndex {
        StdIndex {
            rust_version: "1.85.0-test".to_string(),
            generated_at: "2026-01-01T00:00:00Z".to_string(),
            format_version: 42,
            functions: vec![],
            impls: vec![
                TraitImpl {
                    trait_path: "core::fmt::Display".to_string(),
                    trait_name: "Display".to_string(),
                    for_type: "String".to_string(),
                    type_params: vec![],
                    where_predicates: vec![],
                    associated_types: vec![],
                    methods: vec![MethodSig::simple("fmt")],
                },
                TraitImpl {
                    trait_path: "core::iter::traits::collect::FromIterator".to_string(),
                    trait_name: "FromIterator".to_string(),
                    for_type: "Vec<T>".to_string(),
                    type_params: vec!["T".to_string()],
                    where_predicates: vec![],
                    associated_types: vec![],
                    methods: vec![MethodSig::simple("from_iter")],
                },
                TraitImpl {
                    trait_path: "core::iter::traits::collect::FromIterator".to_string(),
                    trait_name: "FromIterator".to_string(),
                    for_type: "HashMap<K, V>".to_string(),
                    type_params: vec!["K: Eq + Hash".to_string(), "V".to_string()],
                    where_predicates: vec![],
                    associated_types: vec![],
                    methods: vec![MethodSig::simple("from_iter")],
                },
                TraitImpl {
                    trait_path: "core::iter::traits::collect::IntoIterator".to_string(),
                    trait_name: "IntoIterator".to_string(),
                    for_type: "Vec<T>".to_string(),
                    type_params: vec!["T".to_string()],
                    where_predicates: vec![],
                    associated_types: vec![("Item".to_string(), "T".to_string())],
                    methods: vec![MethodSig::simple("into_iter")],
                },
                TraitImpl {
                    trait_path: "core::iter::traits::collect::IntoIterator".to_string(),
                    trait_name: "IntoIterator".to_string(),
                    for_type: "&Vec<T>".to_string(),
                    type_params: vec!["'a".to_string(), "T".to_string()],
                    where_predicates: vec![],
                    associated_types: vec![],
                    methods: vec![MethodSig::simple("into_iter")],
                },
                TraitImpl {
                    trait_path: "core::clone::Clone".to_string(),
                    trait_name: "Clone".to_string(),
                    for_type: "Vec<T>".to_string(),
                    type_params: vec!["T: Clone".to_string()],
                    where_predicates: vec![],
                    associated_types: vec![],
                    methods: vec![MethodSig::simple("clone")],
                },
                TraitImpl {
                    trait_path: "core::ops::deref::Deref".to_string(),
                    trait_name: "Deref".to_string(),
                    for_type: "Vec<T>".to_string(),
                    type_params: vec!["T".to_string()],
                    where_predicates: vec![],
                    associated_types: vec![("Target".to_string(), "[T]".to_string())],
                    methods: vec![MethodSig::simple("deref")],
                },
                TraitImpl {
                    trait_path: "core::fmt::Display".to_string(),
                    trait_name: "Display".to_string(),
                    for_type: "i32".to_string(),
                    type_params: vec![],
                    where_predicates: vec![],
                    associated_types: vec![],
                    methods: vec![MethodSig::simple("fmt")],
                },
            ],
        }
    }

    // ─── short_path ──────────────────────────────────────────────────

    #[test]
    fn test_short_path_full_path() {
        assert_eq!(short_path("std::collections::hash_map::HashMap"), "HashMap");
    }

    #[test]
    fn test_short_path_already_short() {
        assert_eq!(short_path("Vec"), "Vec");
    }

    #[test]
    fn test_short_path_single_segment() {
        assert_eq!(short_path("i32"), "i32");
    }

    #[test]
    fn test_short_path_empty() {
        assert_eq!(short_path(""), "");
    }

    #[test]
    fn test_short_path_trailing_colons() {
        // Edge case: should not panic
        assert_eq!(short_path("foo::"), "");
    }

    #[test]
    fn test_short_path_leading_colons() {
        assert_eq!(short_path("::foo::Bar"), "Bar");
    }

    // ─── find_impls_for ──────────────────────────────────────────────

    #[test]
    fn test_find_impls_for_exact_name() {
        let index = sample_index();
        let results = index.find_impls_for("String");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].trait_name, "Display");
    }

    #[test]
    fn test_find_impls_for_generic_type() {
        let index = sample_index();
        let results = index.find_impls_for("Vec");
        // Vec<T>, &Vec<T> all match
        assert!(
            results.len() >= 4,
            "Expected at least 4 Vec impls, got {}",
            results.len()
        );
    }

    #[test]
    fn test_find_impls_for_substring_match() {
        let index = sample_index();
        // "ec" matches both "Vec<T>" and "&Vec<T>"
        let results = index.find_impls_for("ec");
        assert!(results.len() >= 4);
    }

    #[test]
    fn test_find_impls_for_no_match() {
        let index = sample_index();
        let results = index.find_impls_for("NonExistentType");
        assert!(results.is_empty());
    }

    #[test]
    fn test_find_impls_for_empty_query() {
        let index = sample_index();
        // Empty string matches everything
        let results = index.find_impls_for("");
        assert_eq!(results.len(), index.impls.len());
    }

    #[test]
    fn test_find_impls_for_case_sensitive() {
        let index = sample_index();
        // "vec" should NOT match "Vec" — it's case-sensitive
        let results = index.find_impls_for("vec");
        assert!(
            results.is_empty(),
            "Search should be case-sensitive, but found matches for 'vec'"
        );
    }

    // ─── find_implementors ───────────────────────────────────────────

    #[test]
    fn test_find_implementors_by_name() {
        let index = sample_index();
        let results = index.find_implementors("Display");
        assert_eq!(results.len(), 2); // String, i32
    }

    #[test]
    fn test_find_implementors_by_path_substring() {
        let index = sample_index();
        let results = index.find_implementors("core::fmt");
        assert_eq!(results.len(), 2); // Display for String, Display for i32
    }

    #[test]
    fn test_find_implementors_no_match() {
        let index = sample_index();
        let results = index.find_implementors("Serialize");
        assert!(results.is_empty());
    }

    #[test]
    fn test_find_implementors_exact_name() {
        let index = sample_index();
        let results = index.find_implementors("FromIterator");
        assert_eq!(results.len(), 2); // Vec<T>, HashMap<K, V>
    }

    // ─── implements ──────────────────────────────────────────────────

    #[test]
    fn test_implements_positive() {
        let index = sample_index();
        assert!(index.implements("String", "Display"));
        assert!(index.implements("Vec", "FromIterator"));
        assert!(index.implements("Vec", "IntoIterator"));
        assert!(index.implements("Vec", "Clone"));
        assert!(index.implements("Vec", "Deref"));
        assert!(index.implements("HashMap", "FromIterator"));
    }

    #[test]
    fn test_implements_negative() {
        let index = sample_index();
        assert!(!index.implements("String", "FromIterator"));
        assert!(!index.implements("i32", "Clone")); // Not in our sample
        assert!(!index.implements("HashMap", "Display"));
    }

    #[test]
    fn test_implements_partial_type_match() {
        let index = sample_index();
        // "ap" matches "HashMap<K, V>" since contains() is used
        assert!(index.implements("ap", "FromIterator"));
    }

    #[test]
    fn test_implements_by_trait_path() {
        let index = sample_index();
        // Should also match via trait_path.contains()
        assert!(index.implements("String", "core::fmt::Display"));
    }

    // ─── stats ───────────────────────────────────────────────────────

    #[test]
    fn test_stats_counts() {
        let index = sample_index();
        let stats = index.stats();
        assert_eq!(stats.total_impls, 8);
        assert_eq!(stats.unique_traits, 5); // Display, FromIterator, IntoIterator, Clone, Deref
    }

    #[test]
    fn test_stats_top_traits_sorted() {
        let index = sample_index();
        let stats = index.stats();
        // top_traits should be sorted by count descending
        for window in stats.top_traits.windows(2) {
            assert!(
                window[0].1 >= window[1].1,
                "Top traits not sorted: {:?} should be >= {:?}",
                window[0],
                window[1]
            );
        }
    }

    #[test]
    fn test_stats_empty_index() {
        let index = StdIndex {
            rust_version: "test".to_string(),
            generated_at: "now".to_string(),
            format_version: 1,
            functions: vec![],
            impls: vec![],
        };
        let stats = index.stats();
        assert_eq!(stats.total_impls, 0);
        assert_eq!(stats.unique_traits, 0);
        assert_eq!(stats.unique_types, 0);
        assert!(stats.top_traits.is_empty());
    }

    // ─── Serialization roundtrip ─────────────────────────────────────

    #[test]
    fn test_bincode_roundtrip() {
        let index = sample_index();
        let data = bincode::serialize(&index).expect("serialize failed");
        let recovered: StdIndex = bincode::deserialize(&data).expect("deserialize failed");
        assert_eq!(recovered.rust_version, index.rust_version);
        assert_eq!(recovered.impls.len(), index.impls.len());
        for (orig, rec) in index.impls.iter().zip(recovered.impls.iter()) {
            assert_eq!(orig.trait_name, rec.trait_name);
            assert_eq!(orig.trait_path, rec.trait_path);
            assert_eq!(orig.for_type, rec.for_type);
            assert_eq!(orig.type_params, rec.type_params);
            assert_eq!(orig.methods, rec.methods);
        }
    }

    #[test]
    fn test_json_roundtrip() {
        let index = sample_index();
        let json = index.to_json().expect("to_json failed");
        let recovered: StdIndex = serde_json::from_str(&json).expect("from_json failed");
        assert_eq!(recovered.impls.len(), index.impls.len());
        assert_eq!(recovered.rust_version, index.rust_version);
    }

    #[test]
    fn test_bincode_corrupted_data() {
        let result: Result<StdIndex, _> = bincode::deserialize(b"not valid bincode data");
        assert!(result.is_err());
    }

    #[test]
    fn test_json_empty_object() {
        let result: Result<StdIndex, _> = serde_json::from_str("{}");
        assert!(result.is_err());
    }

    // ─── Disk persistence ────────────────────────────────────────────

    #[test]
    fn test_save_and_load_file() {
        let index = sample_index();
        let dir = std::env::temp_dir().join("rustdex_test");
        std::fs::create_dir_all(&dir).ok();
        let path = dir.join("test_index.bin");

        index.save(&path).expect("save failed");
        assert!(path.exists());

        let loaded = StdIndex::load(&path).expect("load failed");
        assert_eq!(loaded.impls.len(), index.impls.len());
        assert_eq!(loaded.rust_version, index.rust_version);
        assert_eq!(loaded.format_version, index.format_version);

        // Verify trait data survived the roundtrip
        for (orig, loaded) in index.impls.iter().zip(loaded.impls.iter()) {
            assert_eq!(orig.trait_name, loaded.trait_name);
            assert_eq!(orig.for_type, loaded.for_type);
            assert_eq!(orig.methods, loaded.methods);
            assert_eq!(orig.type_params, loaded.type_params);
            assert_eq!(orig.associated_types, loaded.associated_types);
        }

        std::fs::remove_file(&path).ok();
        std::fs::remove_dir(&dir).ok();
    }

    #[test]
    fn test_load_nonexistent_file() {
        let result = StdIndex::load(Path::new("/tmp/rustdex_does_not_exist_12345.bin"));
        assert!(result.is_err());
    }

    #[test]
    fn test_save_to_invalid_path() {
        let index = sample_index();
        let result = index.save(Path::new("/nonexistent_dir_12345/test.bin"));
        assert!(result.is_err());
    }

    #[test]
    fn test_save_load_preserves_associated_types() {
        let mut index = sample_index();
        // Add an impl with associated types
        index.impls.push(TraitImpl {
            trait_path: "core::iter::traits::iterator::Iterator".to_string(),
            trait_name: "Iterator".to_string(),
            for_type: "MyIter".to_string(),
            type_params: vec![],
            where_predicates: vec![],
            associated_types: vec![("Item".to_string(), "u32".to_string())],
            methods: vec![MethodSig::simple("next")],
        });

        let dir = std::env::temp_dir().join("rustdex_test_assoc");
        std::fs::create_dir_all(&dir).ok();
        let path = dir.join("test_assoc.bin");

        index.save(&path).expect("save failed");
        let loaded = StdIndex::load(&path).expect("load failed");

        let last = loaded.impls.last().unwrap();
        assert_eq!(last.trait_name, "Iterator");
        assert_eq!(
            last.associated_types,
            vec![("Item".to_string(), "u32".to_string())]
        );

        std::fs::remove_file(&path).ok();
        std::fs::remove_dir(&dir).ok();
    }

    // ─── Edge cases and adversarial inputs ───────────────────────────

    #[test]
    fn test_query_with_angle_brackets() {
        let index = sample_index();
        // Searching for the exact generic type
        let results = index.find_impls_for("Vec<T>");
        assert!(!results.is_empty(), "Should find impls for 'Vec<T>'");
    }

    #[test]
    fn test_query_with_reference_type() {
        let index = sample_index();
        let results = index.find_impls_for("&Vec");
        assert!(!results.is_empty(), "Should find impls for '&Vec'");
        // Should only match &Vec<T>, not Vec<T>
        for r in &results {
            assert!(
                r.for_type.starts_with('&'),
                "Expected reference type, got: {}",
                r.for_type
            );
        }
    }

    #[test]
    fn test_query_special_characters() {
        let index = sample_index();
        // These should just return empty, not panic
        let _ = index.find_impls_for("<>");
        let _ = index.find_impls_for("&&");
        let _ = index.find_impls_for("...");
        let _ = index.find_implementors("***");
        assert!(!index.implements("(*)", "Display"));
    }

    #[test]
    fn test_overlapping_type_names() {
        // "Vec" matches both "Vec<T>" and "&Vec<T>" and "VecDeque<T>"
        let mut index = sample_index();
        index.impls.push(TraitImpl {
            trait_path: "core::clone::Clone".to_string(),
            trait_name: "Clone".to_string(),
            for_type: "VecDeque<T>".to_string(),
            type_params: vec!["T: Clone".to_string()],
            where_predicates: vec![],
            associated_types: vec![],
            methods: vec![MethodSig::simple("clone")],
        });

        let results = index.find_impls_for("Vec");
        // Should match Vec<T>, &Vec<T>, and VecDeque<T>
        let types: Vec<&str> = results.iter().map(|r| r.for_type.as_str()).collect();
        assert!(
            types.iter().any(|t| t.contains("VecDeque")),
            "Should also match VecDeque: {:?}",
            types
        );
    }

    #[test]
    fn test_trait_path_vs_name_distinction() {
        let index = sample_index();
        // find_implementors should match both by exact name and by path substring
        let by_name = index.find_implementors("Display");
        let by_path = index.find_implementors("core::fmt::Display");
        assert_eq!(
            by_name.len(),
            by_path.len(),
            "name search ({}) and path search ({}) should find same results",
            by_name.len(),
            by_path.len()
        );
    }

    #[test]
    fn test_multiple_impls_same_trait_different_types() {
        let index = sample_index();
        let from_iter_impls = index.find_implementors("FromIterator");
        let types: Vec<&str> = from_iter_impls
            .iter()
            .map(|r| r.for_type.as_str())
            .collect();
        assert!(
            types.contains(&"Vec<T>"),
            "FromIterator should include Vec<T>: {:?}",
            types
        );
        assert!(
            types.contains(&"HashMap<K, V>"),
            "FromIterator should include HashMap<K, V>: {:?}",
            types
        );
    }

    // ─── Data model invariants ───────────────────────────────────────

    #[test]
    fn test_trait_impl_fields_non_empty() {
        let index = sample_index();
        for imp in &index.impls {
            assert!(!imp.trait_name.is_empty(), "trait_name should not be empty");
            assert!(!imp.trait_path.is_empty(), "trait_path should not be empty");
            assert!(!imp.for_type.is_empty(), "for_type should not be empty");
            assert!(
                !imp.methods.is_empty(),
                "methods should not be empty for test data"
            );
        }
    }

    #[test]
    fn test_format_version_preserved() {
        let index = sample_index();
        assert_eq!(index.format_version, 42);
        let json = index.to_json().unwrap();
        let recovered: StdIndex = serde_json::from_str(&json).unwrap();
        assert_eq!(recovered.format_version, 42);
    }

    // ─── Full integration tests (requires rust-docs-json) ────────────

    #[test]
    fn test_sysroot_build_and_query() {
        if IndexBuilder::from_sysroot().is_err() {
            eprintln!("Skipping: rust-docs-json not installed");
            return;
        }
        let index = IndexBuilder::from_sysroot()
            .unwrap()
            .build()
            .expect("build failed");
        eprintln!(
            "Built index with {} impls from {} types and {} traits",
            index.impls.len(),
            index.stats().unique_types,
            index.stats().unique_traits
        );

        // ─── Must-pass checks ────────────────────────────────────────
        // These are well-known std trait impls that MUST be present.

        // alloc types
        assert!(
            index.implements("Vec", "IntoIterator"),
            "Vec must impl IntoIterator"
        );
        assert!(
            index.implements("Vec", "FromIterator"),
            "Vec must impl FromIterator"
        );
        assert!(index.implements("Vec", "Clone"), "Vec must impl Clone");
        assert!(index.implements("Vec", "Deref"), "Vec must impl Deref");
        assert!(
            index.implements("String", "Display"),
            "String must impl Display"
        );
        assert!(index.implements("String", "From"), "String must impl From");
        assert!(
            index.implements("HashMap", "FromIterator"),
            "HashMap must impl FromIterator"
        );
        assert!(
            index.implements("HashMap", "IntoIterator"),
            "HashMap must impl IntoIterator"
        );

        // core/primitive types
        assert!(index.implements("i32", "Add"), "i32 must impl Add");
        assert!(index.implements("i32", "Display"), "i32 must impl Display");
        assert!(
            index.implements("bool", "Display"),
            "bool must impl Display"
        );
        assert!(index.implements("f64", "From"), "f64 must impl From");

        // std types
        assert!(
            index.implements("PathBuf", "From"),
            "PathBuf must impl From"
        );

        // ─── Negative checks ─────────────────────────────────────────
        // Note: implements() uses substring matching on for_type, so
        // common type names like "i32" or "HashMap" can appear inside
        // generic params of other types (e.g. IntoIter<HashMap<...>>).
        // Use made-up names that can't match any real type.
        assert!(
            !index.implements("UnknownType12345", "Display"),
            "Made-up type should not impl Display"
        );
        assert!(
            !index.implements("UnknownType12345", "Iterator"),
            "Made-up type should not impl Iterator"
        );
        assert!(
            !index.implements("UnknownType12345", "FromIterator"),
            "Made-up type should not impl FromIterator"
        );

        // ─── Sanity checks ───────────────────────────────────────────
        let stats = index.stats();
        assert!(
            stats.total_impls > 10000,
            "Expected >10000 impls, got {}",
            stats.total_impls
        );
        assert!(
            stats.unique_traits > 100,
            "Expected >100 traits, got {}",
            stats.unique_traits
        );
        assert!(
            stats.unique_types > 500,
            "Expected >500 types, got {}",
            stats.unique_types
        );
    }

    #[test]
    fn test_sysroot_roundtrip_file() {
        if IndexBuilder::from_sysroot().is_err() {
            eprintln!("Skipping: rust-docs-json not installed");
            return;
        }
        let index = IndexBuilder::from_sysroot()
            .unwrap()
            .build()
            .expect("build failed");
        let path = std::env::temp_dir().join("rustdex_integration_test.bin");

        index.save(&path).expect("save failed");
        let loaded = StdIndex::load(&path).expect("load failed");

        assert_eq!(
            loaded.impls.len(),
            index.impls.len(),
            "Impl count mismatch after roundtrip: {} vs {}",
            loaded.impls.len(),
            index.impls.len()
        );
        assert_eq!(loaded.rust_version, index.rust_version);
        assert_eq!(loaded.format_version, index.format_version);

        // Spot-check a few specific impls survived roundtrip
        assert!(
            loaded.implements("Vec", "IntoIterator"),
            "Vec IntoIterator lost in roundtrip"
        );
        assert!(
            loaded.implements("HashMap", "FromIterator"),
            "HashMap FromIterator lost in roundtrip"
        );

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_sysroot_json_roundtrip() {
        if IndexBuilder::from_sysroot().is_err() {
            eprintln!("Skipping: rust-docs-json not installed");
            return;
        }
        let index = IndexBuilder::from_sysroot()
            .unwrap()
            .build()
            .expect("build failed");
        let json = index.to_json().expect("to_json failed");

        // JSON should be non-trivial size
        assert!(
            json.len() > 100_000,
            "JSON should be >100KB, got {} bytes",
            json.len()
        );

        let recovered: StdIndex = serde_json::from_str(&json).expect("JSON parse failed");
        assert_eq!(recovered.impls.len(), index.impls.len());
        assert!(
            recovered.implements("Vec", "Clone"),
            "Vec Clone lost in JSON roundtrip"
        );
    }

    #[test]
    fn test_single_crate_vs_multi_crate() {
        // If only std.json is used, we should get fewer impls than with all 3
        let dir = match sysroot_json_dir() {
            Ok(d) => d,
            Err(_) => {
                eprintln!("Skipping: sysroot not found");
                return;
            }
        };
        let std_path = dir.join("std.json");
        if !std_path.exists() {
            return;
        }

        let std_only = IndexBuilder::from_path(&std_path)
            .build()
            .expect("std-only build failed");
        let all_crates = IndexBuilder::from_sysroot()
            .unwrap()
            .build()
            .expect("full build failed");

        eprintln!(
            "std-only: {} impls, all-crates: {} impls",
            std_only.impls.len(),
            all_crates.impls.len()
        );
        assert!(
            all_crates.impls.len() > std_only.impls.len(),
            "Multi-crate ({}) should have more impls than std-only ({})",
            all_crates.impls.len(),
            std_only.impls.len()
        );

        // Vec+IntoIterator should be in all-crates but NOT in std-only
        assert!(
            !std_only.implements("Vec", "IntoIterator"),
            "Vec IntoIterator should NOT be in std-only (it's in alloc)"
        );
        assert!(
            all_crates.implements("Vec", "IntoIterator"),
            "Vec IntoIterator must be in all-crates"
        );
    }
}
