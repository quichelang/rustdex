# Rustdex

A compact, queryable index of Rust standard library trait implementations.

## What it does

Rustdex reads the machine-readable documentation that ships with your Rust toolchain (`rustdoc --output-format json`) and extracts every trait implementation into a small binary index. You can then query this index to answer questions like:

- "Does `HashMap` implement `FromIterator`?" → **Yes**
- "What traits does `Vec` implement?" → `IntoIterator`, `FromIterator`, `Index`, `Deref`, …
- "Which types implement `Display`?" → `String`, `i32`, `bool`, …

## Why it's useful

If you're building a **compiler**, **transpiler**, **code generator**, or **IDE plugin** that targets Rust, you often need to know what methods and traits are available on standard types — without parsing the entire standard library yourself. Rustdex gives you that information in a single, fast, <100KB binary file.

### Example use cases

- **Transpilers** (like [Elevate](https://github.com/jagtesh/elevate)) need to know if `.collect()` can produce a `HashMap` from an iterator of tuples
- **Code generators** need to know if a type supports `Display` to decide how to format it
- **Language servers** can use the index for auto-completion of trait methods
- **Linters** can check if a type actually implements a trait before suggesting a method call

## Quick start

```bash
# Install
cargo install --path .

# Build the index from your current Rust toolchain
rustdex build

# Query: what traits does HashMap implement?
rustdex query HashMap

# Query: what types implement FromIterator?
rustdex query --trait FromIterator

# Check: does Vec implement IntoIterator?
rustdex check Vec IntoIterator
# ✅ Vec implements IntoIterator

# Show statistics
rustdex stats
```

## Library usage

```rust
use rustdex::{StdIndex, IndexBuilder};

// Build from current toolchain's std.json
let index = IndexBuilder::from_sysroot()?.build()?;

// Query
if index.implements("HashMap", "FromIterator") {
    println!("HashMap can be collected from an iterator!");
}

// Find all traits for a type
for imp in index.find_impls_for("Vec") {
    println!("Vec: {}", imp.trait_name);
}

// Save for later (bincode, ~80KB)
index.save_to_sysroot()?;

// Load a previously built index (fast — no parsing needed)
let cached = StdIndex::load_from_sysroot()?;
```

## How it works

1. **Input**: Reads `std.json` from `$(rustc --print sysroot)/share/doc/rust/json/` (requires the `rust-docs-json` component)
2. **Extract**: Parses all trait implementation blocks using the `rustdoc-types` crate
3. **Index**: Builds a compact representation with trait paths, implementing types, generic parameters, and method names
4. **Output**: Serializes to bincode (default) or JSON (with `--json` flag) alongside the source JSON in the sysroot

## Prerequisites

> Note: rustdex depends on rustdoc JSON features that are available only on the Rust **nightly** toolchain. Generating or using the rustdex index therefore requires a nightly toolchain with the JSON docs component.

```bash
# Install nightly toolchain and the JSON documentation component for nightly
rustup toolchain install nightly
rustup component add rust-docs-json --toolchain nightly
```

This repository includes a `rust-toolchain.toml` that requests `nightly` and the `rust-docs-json` component; `cargo` run inside the repo will automatically use that toolchain (rustup will install it if needed).

## Index location

The index is saved alongside the rustdoc JSON in your toolchain's sysroot:

```
~/.rustup/toolchains/<toolchain>/share/doc/rust/json/rustdex_<version>.bin
```

This is automatically version-specific — each Rust version gets its own index file. Run `rustdex path` to see the exact location.

## Features

| Feature | Default | Description |
|---------|---------|-------------|
| `json-export` | off | Enables `StdIndex::to_json()` in the library API |

The CLI always supports `--json` regardless of this feature flag.

## License

BSD 3-Clause — see [LICENSE](LICENSE).
