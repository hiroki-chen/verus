use std::fs;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context, Result};
use colored::Colorize;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::builder::Builder;
use crate::util::project_root;

pub(crate) fn test_runner(suite: Option<String>, release: bool) -> Result<()> {
    println!("{} Deko Test Runner", "🧪".bright_cyan().bold());

    let project_root = project_root();
    let tests_dir = project_root.join("tests");

    if !tests_dir.exists() {
        bail!("Tests directory not found at: {:?}", tests_dir);
    }

    let available_suites = fs::read_dir(&tests_dir)?
        .filter_map(|entry| {
            let entry = entry.ok()?;
            if entry.file_type().ok()?.is_dir() {
                entry.file_name().to_str().map(|s| s.to_string())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    if available_suites.is_empty() {
        println!("⚠ No test suites found in tests directory");
        return Ok(());
    }

    let suites_to_run = if let Some(suite_name) = suite {
        if !available_suites.contains(&suite_name) {
            println!("❌ Test suite '{}' not found", suite_name.red());
            println!("Available suites: {}", available_suites.join(", "));
            bail!("Invalid test suite specified");
        }
        vec![suite_name]
    } else {
        available_suites
    };

    println!("📋 Running test suites: {}", suites_to_run.join(", ").bright_white());
    if release {
        println!("🚀 Running in release mode");
    }

    let builder = Builder::new("snp".to_string());
    let verus_binary = builder.find_verus_binary()?;
    let z3_binary = builder.find_z3_binary()?;

    std::env::set_var("VERUS_Z3_PATH", &z3_binary);
    std::env::set_var("RUSTC_BOOTSTRAP", "1");
    if verus_binary != PathBuf::from("verus") {
        let verus_dir = verus_binary.parent().unwrap_or_else(|| Path::new("."));
        let current_path = std::env::var("PATH").unwrap_or_default();
        let new_path = format!("{}:{}", verus_dir.display(), current_path);
        std::env::set_var("PATH", new_path);
    }

    let mut all_passed = true;
    std::env::set_current_dir(&project_root)?;

    for suite in &suites_to_run {
        println!(
            "\n{} {} {}",
            "═".repeat(20),
            format!("Testing {}", suite).bright_cyan().bold(),
            "═".repeat(20)
        );

        println!("🔨 Building test binary for '{}'...", suite);

        let mut cmd = Command::new("cargo");
        let suite_path = tests_dir.join(suite).join("Cargo.toml");
        if !suite_path.exists() {
            println!("✗ Test suite directory not found: {:?}", suite_path);
            all_passed = false;
            continue;
        }

        cmd.arg("verus").arg("build").arg("--manifest-path").arg(suite_path);
        if release {
            cmd.arg("--release");
        }

        println!("Running: {:?}", cmd);

        let output =
            cmd.output().with_context(|| format!("Failed to build test suite: {}", suite))?;

        if !output.status.success() {
            println!("✗ Failed to build test suite '{}'", suite);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);

            if !stdout.is_empty() {
                println!("{}", "BUILD STDOUT:".bright_yellow());
                println!("{}", stdout);
            }
            if !stderr.is_empty() {
                println!("{}", "BUILD STDERR:".bright_yellow());
                println!("{}", stderr);
            }

            all_passed = false;
            continue;
        }

        println!("✓ Built test binary for '{}'", suite);

        let profile = if release { "release" } else { "debug" };
        let target_dir = project_root.join("target").join(profile);
        let binary_path = target_dir.join(suite);

        if !binary_path.exists() {
            println!("✗ Test binary not found at: {:?}", binary_path);
            all_passed = false;
            continue;
        }

        println!("🚀 Executing test binary: {:?}", binary_path);

        let mut test_cmd = Command::new(&binary_path);
        test_cmd.stdout(Stdio::inherit()).stderr(Stdio::inherit());

        let test_status = test_cmd
            .status()
            .with_context(|| format!("Failed to execute test binary: {:?}", binary_path))?;

        if test_status.success() {
            println!("✓ Test suite '{}' {}", suite, "PASSED".bright_green().bold());
        } else {
            println!("✗ Test suite '{}' {}", suite, "FAILED".bright_red().bold());
            all_passed = false;
        }
    }

    println!("\n{}", "═".repeat(60));
    if all_passed {
        println!("🎉 All tests {} ({})", "PASSED".bright_green().bold(), suites_to_run.len());
    } else {
        println!("💥 Some tests {} ({})", "FAILED".bright_red().bold(), suites_to_run.len());
        bail!("Test execution failed");
    }

    Ok(())
}

pub(crate) fn line_count() -> Result<()> {
    println!("{} Verus Line Count Tool", "📊".bright_cyan().bold());

    if which::which("line_count").is_err() {
        println!("{} `line_count` not found, installing it from Verus...", "❌".bright_cyan());
        let mut cmd = Command::new("cargo");
        cmd.arg("install")
            .arg("line_count")
            .arg("--git")
            .arg("https://github.com/verus-lang/verus");

        println!("Running: {:?}", cmd);
        let output = cmd.output().context("Failed to install line_count tool")?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            println!("❌ Failed to install line_count:");
            println!("STDOUT: {}", stdout);
            println!("STDERR: {}", stderr);
            bail!("line_count installation failed");
        }
    }

    println!("{} Generating dependency information...", "🔍".bright_yellow());

    let project_root = project_root();
    let packages = vec!["deko-core", "deko-std"];

    let builder = Builder::new("snp".to_string());
    let verus_binary = builder.find_verus_binary()?;
    let z3_binary = builder.find_z3_binary()?;

    std::env::set_var("VERUS_Z3_PATH", &z3_binary);
    std::env::set_var("RUSTC_BOOTSTRAP", "1");

    if verus_binary != PathBuf::from("verus") {
        let verus_dir = verus_binary.parent().unwrap_or_else(|| Path::new("."));
        let current_path = std::env::var("PATH").unwrap_or_default();
        let new_path = format!("{}:{}", verus_dir.display(), current_path);
        std::env::set_var("PATH", new_path);
    }

    for package in &packages {
        println!("📦 Processing package: {}", package.bright_white());

        let mut cmd = Command::new("cargo");
        cmd.arg("verus")
            .arg("verify")
            .arg("--package")
            .arg(package)
            .arg("--features")
            .arg("snp, vstd/allow_panic, vstd/alloc, deko-std/alloc")
            .arg("--")
            .arg("--emit=dep-info");

        println!("Running: {:?}", cmd);

        let output = cmd
            .output()
            .with_context(|| format!("Failed to run cargo verus verify for {}", package))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            println!("❌ Failed to generate dependency info for {}:", package.red());
            println!("STDOUT: {}", stdout);
            println!("STDERR: {}", stderr);
            continue;
        }

        println!("✓ Generated dependency information for {}", package.green());
    }

    let dep_path = project_root.join("target").join("debug");
    for package in &packages {
        let dep_file = dep_path.join(format!("lib{}.d", package.replace("-", "_")));
        if !dep_file.exists() {
            println!("⚠ Dependency file not found for {}: {:?}", package.yellow(), dep_file);
            continue;
        }

        println!("📄 Parsing dependency file: {:?}", dep_file);

        let content = fs::read_to_string(&dep_file)
            .with_context(|| format!("Failed to read dep-info file: {:?}", dep_file))?;
        let content = content
            .split(' ')
            .filter_map(|f| if f.contains(".rs") || f.contains(".rlib") { Some(f) } else { None })
            .collect::<Vec<_>>()
            .join(" ");

        let file_handle = fs::File::create(&dep_file)
            .with_context(|| format!("Failed to open dep-info file for writing: {:?}", dep_file))?;
        let mut writer = BufWriter::new(file_handle);
        writer
            .write_all(content.as_bytes())
            .with_context(|| format!("Failed to write to dep-info file: {:?}", dep_file))?;
        writer.flush().with_context(|| format!("Failed to flush dep-info file: {:?}", dep_file))?;

        let mut cmd = Command::new("line_count");
        cmd.arg(dep_file.display().to_string());

        println!("Running: {:?}", cmd);

        let out = cmd.output().with_context(|| {
            format!("Failed to run line_count tool on dep-info file: {:?}", dep_file)
        })?;

        let output_file_path = project_root
            .join("target")
            .join("debug")
            .join(format!("line_count_output_{}.txt", package.replace("-", "_")));
        let mut output_file = fs::File::create(&output_file_path).with_context(|| {
            format!("Failed to create line count output file: {:?}", output_file_path)
        })?;
        output_file.write_all(&out.stdout).with_context(|| {
            format!("Failed to write to line count output file: {:?}", output_file_path)
        })?;
    }

    Ok(())
}

pub(crate) fn pretty(paths: Vec<PathBuf>) -> Result<()> {
    let root = project_root();

    let rs_files = if !paths.is_empty() {
        paths
    } else {
        let mut files = vec![];
        for entry in walkdir::WalkDir::new(&root) {
            let entry = entry?;
            let path = entry.path();

            if entry.file_type().is_file()
                && path.extension().and_then(|s| s.to_str()) == Some("rs")
                && path.to_str().is_some_and(|s| {
                    s.contains("deko") && !s.contains("target") && !s.contains("deko-macros")
                })
            {
                files.push(path.to_path_buf());
            }
        }
        files
    };

    rs_files.par_iter().for_each(|file| {
        let mut cmd = Command::new("verusfmt");
        let _ = cmd.arg(file).output();
    });

    println!("✓ Formatted {} files", rs_files.len());
    Ok(())
}
