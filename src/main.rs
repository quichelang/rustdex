//! Rustdex CLI — build and query Rust standard library trait indexes.
//!
//! Usage:
//!   rustdex build              Build index from current toolchain's std.json
//!   rustdex build --json       Also export as JSON
//!   rustdex build -o FILE      Write to custom path instead of sysroot
//!   rustdex query TYPE         Find all traits implemented by TYPE
//!   rustdex query --trait NAME Find all types implementing NAME
//!   rustdex check TYPE TRAIT   Check if TYPE implements TRAIT
//!   rustdex stats              Show index statistics
//!   rustdex path               Print the sysroot index path

use rustdex::{IndexBuilder, StdIndex};
use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    if args.is_empty() {
        print_help();
        return;
    }

    let result = match args[0].as_str() {
        "build" => cmd_build(&args[1..]),
        "query" => cmd_query(&args[1..]),
        "check" => cmd_check(&args[1..]),
        "stats" => cmd_stats(&args[1..]),
        "path" => cmd_path(),
        "help" | "--help" | "-h" => {
            print_help();
            Ok(())
        }
        other => Err(format!(
            "Unknown command: {other}. Run `rustdex help` for usage."
        )),
    };

    if let Err(e) = result {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn cmd_build(args: &[String]) -> Result<(), String> {
    let mut output_path: Option<PathBuf> = None;
    let mut export_json = false;
    let mut input_path: Option<PathBuf> = None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" | "--output" => {
                i += 1;
                output_path = Some(PathBuf::from(
                    args.get(i).ok_or("Missing output path after -o")?,
                ));
            }
            "--json" => export_json = true,
            "-i" | "--input" => {
                i += 1;
                input_path = Some(PathBuf::from(
                    args.get(i).ok_or("Missing input path after -i")?,
                ));
            }
            _ => return Err(format!("Unknown build flag: {}", args[i])),
        }
        i += 1;
    }

    let builder = if let Some(path) = input_path {
        eprintln!("Reading rustdoc JSON from: {}", path.display());
        IndexBuilder::from_path(path)
    } else {
        eprintln!("Reading std.json from sysroot...");
        IndexBuilder::from_sysroot()?
    };

    eprintln!("Parsing and extracting trait implementations...");
    let index = builder.build()?;
    let stats = index.stats();

    eprintln!(
        "Extracted {} trait impls ({} unique traits, {} unique types)",
        stats.total_impls, stats.unique_traits, stats.unique_types,
    );

    // Save bincode
    let saved_path = if let Some(path) = output_path {
        index.save(&path)?;
        path
    } else {
        index.save_to_sysroot()?
    };

    let file_size = std::fs::metadata(&saved_path).map(|m| m.len()).unwrap_or(0);
    eprintln!(
        "Saved index to: {} ({:.1} KB)",
        saved_path.display(),
        file_size as f64 / 1024.0
    );

    // Optionally export JSON alongside
    if export_json {
        let json_path = saved_path.with_extension("json");
        let json = index.to_json()?;
        std::fs::write(&json_path, &json).map_err(|e| format!("write error: {e}"))?;
        let json_size = json.len();
        eprintln!(
            "Exported JSON to: {} ({:.1} KB)",
            json_path.display(),
            json_size as f64 / 1024.0
        );
    }

    Ok(())
}

fn cmd_query(args: &[String]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: rustdex query TYPE or rustdex query --trait TRAIT".into());
    }

    let index = load_index(args)?;

    if args[0] == "--trait" || args[0] == "-t" {
        let trait_name = args.get(1).ok_or("Missing trait name after --trait")?;
        let impls = index.find_implementors(trait_name);
        if impls.is_empty() {
            println!("No types found implementing '{trait_name}'");
        } else {
            println!("Types implementing '{trait_name}':");
            for imp in impls {
                let params = if imp.type_params.is_empty() {
                    String::new()
                } else {
                    format!(" where {}", imp.type_params.join(", "))
                };
                println!("  {} → {}{params}", imp.for_type, imp.trait_path);
            }
        }
    } else {
        let type_name = &args[0];
        let impls = index.find_impls_for(type_name);
        if impls.is_empty() {
            println!("No trait impls found for '{type_name}'");
        } else {
            println!("Trait impls for '{type_name}':");
            for imp in impls {
                let methods = if imp.methods.is_empty() {
                    String::new()
                } else {
                    format!(
                        " [{}]",
                        imp.methods
                            .iter()
                            .map(|m| m.name.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                println!("  {}{methods}", imp.trait_name);
            }
        }
    }

    Ok(())
}

fn cmd_check(args: &[String]) -> Result<(), String> {
    if args.len() < 2 {
        return Err("Usage: rustdex check TYPE TRAIT".into());
    }

    let index = load_index(args)?;
    let type_name = &args[0];
    let trait_name = &args[1];

    if index.implements(type_name, trait_name) {
        println!("✅ {type_name} implements {trait_name}");

        // Show the specific impl
        let impls: Vec<_> = index
            .impls
            .iter()
            .filter(|imp| {
                imp.for_type.contains(type_name.as_str()) && imp.trait_name == *trait_name
            })
            .collect();
        for imp in impls {
            if !imp.type_params.is_empty() {
                println!("   where {}", imp.type_params.join(", "));
            }
            if !imp.methods.is_empty() {
                println!(
                    "   methods: {}",
                    imp.methods
                        .iter()
                        .map(|m| m.name.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
    } else {
        println!("❌ {type_name} does NOT implement {trait_name}");
    }

    Ok(())
}

fn cmd_stats(args: &[String]) -> Result<(), String> {
    let index = load_index(args)?;
    let stats = index.stats();

    println!("Rustdex Index v{}", index.rust_version);
    println!("Generated: {}", index.generated_at);
    println!("Format version: {}", index.format_version);
    println!();
    println!("Total impls:   {}", stats.total_impls);
    println!("Unique traits: {}", stats.unique_traits);
    println!("Unique types:  {}", stats.unique_types);
    println!();
    println!("Top traits by implementation count:");
    for (name, count) in &stats.top_traits {
        println!("  {count:4}  {name}");
    }

    Ok(())
}

fn cmd_path() -> Result<(), String> {
    let version = rustdex::rust_version()?;
    let dir = rustdex::sysroot_json_dir()?;
    let path = dir.join(format!("rustdex_{version}.bin"));
    println!("{}", path.display());
    if path.exists() {
        let size = std::fs::metadata(&path).map(|m| m.len()).unwrap_or(0);
        eprintln!("(exists, {:.1} KB)", size as f64 / 1024.0);
    } else {
        eprintln!("(not yet built — run `rustdex build`)");
    }
    Ok(())
}

fn load_index(args: &[String]) -> Result<StdIndex, String> {
    // Check for --index flag
    for (i, arg) in args.iter().enumerate() {
        if (arg == "--index" || arg == "-I") && i + 1 < args.len() {
            return StdIndex::load(&PathBuf::from(&args[i + 1]));
        }
    }
    StdIndex::load_from_sysroot()
}

fn print_help() {
    eprintln!(
        r#"rustdex — A compact index of Rust standard library trait implementations

USAGE:
    rustdex <COMMAND> [OPTIONS]

COMMANDS:
    build              Build the index from the current toolchain's std.json
        -o, --output   Write to a custom file instead of sysroot
        -i, --input    Read from a custom rustdoc JSON file
        --json         Also export as JSON alongside the bincode index
    query TYPE         Find all traits implemented by TYPE
    query --trait NAME Find all types implementing a given trait
    check TYPE TRAIT   Check if TYPE implements TRAIT
    stats              Show index statistics
    path               Print the default index path
    help               Show this help message

EXAMPLES:
    rustdex build
    rustdex build --json
    rustdex query HashMap
    rustdex query --trait FromIterator
    rustdex check HashMap FromIterator
    rustdex stats"#
    );
}
