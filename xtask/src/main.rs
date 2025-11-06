use std::fs::{self, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context, Result};
use clap::{Parser, Subcommand, ValueEnum};
use colored::Colorize;
use git2::Repository;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use serde::Deserialize;
use serde_json;

// Cargo JSON message structures for parsing build output
#[derive(Deserialize, Debug)]
#[serde(tag = "reason")]
enum CargoMessage {
    #[serde(rename = "compiler-message")]
    CompilerMessage { message: CompilerMessage },
    #[serde(rename = "build-finished")]
    BuildFinished { success: bool },
    #[serde(other)]
    Other,
}

#[derive(Deserialize, Debug)]
struct CompilerMessage {
    message: String,
    level: String,
    spans: Vec<Span>,
    children: Vec<ChildMessage>,
    rendered: Option<String>,
}

#[derive(Deserialize, Debug)]
struct Span {
    file_name: String,
    line_start: u32,
    column_start: u32,
    is_primary: bool,
    text: Vec<SpanText>,
    label: Option<String>,
}

#[derive(Deserialize, Debug)]
struct SpanText {
    text: String,
    // highlight_start: u32,
    // highlight_end: u32,
}

#[derive(Deserialize, Debug)]
struct ChildMessage {
    message: String,
    level: String,
}

// Build summary for tracking compilation results
#[derive(Debug, Default)]
struct BuildSummary {
    errors: Vec<CompilerMessage>,
    warnings: Vec<CompilerMessage>,
    notes: Vec<CompilerMessage>,
    successful: bool,
}

impl BuildSummary {
    fn add_message(&mut self, msg: CompilerMessage) {
        match msg.level.as_str() {
            "error" => self.errors.push(msg),
            "warning" => self.warnings.push(msg),
            "note" | "help" => self.notes.push(msg),
            _ => {}
        }
    }

    fn print_summary(&self) {
        println!("\n{}", "=== BUILD SUMMARY ===".bright_cyan().bold());

        if self.successful {
            println!("{} {}", "✓".green().bold(), "Build completed successfully".green());

            // Show notes/diagnostics count if there are any
            if !self.notes.is_empty() {
                println!(
                    "{} {} diagnostics/notes",
                    "ℹ".blue(),
                    self.notes.len().to_string().blue()
                );
            }
        } else {
            println!("{} {}", "✗".red().bold(), "Build failed".red());
        }

        if !self.errors.is_empty() {
            println!("{} {} errors", "●".red(), self.errors.len().to_string().red().bold());
        }

        // Print detailed error information with diagnostics after each error

        for (i, error) in self.errors.iter().enumerate() {
            // First print the error
            self.print_formatted_message(error, i + 1);
        }

        for note in &self.notes {
            if let Some(rendered) = &note.rendered {
                println!("\n{} {}", "📋".blue(), "Related diagnostic expansion:".blue().bold());
                self.print_verification_failure_details(rendered);
            }
        }
    }

    fn print_formatted_message(&self, msg: &CompilerMessage, index: usize) {
        let level_color = match msg.level.as_str() {
            "error" => "red",
            "warning" => "yellow",
            "note" => "blue",
            "help" => "cyan",
            _ => "white",
        };

        println!(
            "\n{}. {}: {}",
            index.to_string().bright_white().bold(),
            msg.level.to_uppercase().color(level_color).bold(),
            msg.message.color(level_color)
        );

        if let Some(rendered) = &msg.rendered {
            self.print_verification_failure_details(rendered);
        } else if let Some(rendered) = &msg.rendered {
            // For other errors, show key information
            self.print_error_summary(rendered, level_color);
        } else {
            // Fallback to manual formatting if no rendered field
            self.print_manual_formatting(msg, level_color);
        }
    }

    fn print_verification_failure_details(&self, rendered: &str) {
        let lines: Vec<&str> = rendered.lines().collect();
        let mut file_location = String::new();
        let mut in_expansion = false;

        // Extract file location
        for line in &lines {
            if line.contains("-->") {
                file_location = line.trim().to_string();
                break;
            }
        }

        if !file_location.is_empty() {
            println!("   {} {}", "Location:".bright_blue(), file_location.bright_white());
        }

        // Determine if this is a diagnostic expansion
        let is_diagnostic = rendered.contains("diagnostics via expansion");
        if is_diagnostic {
            println!("   {}", "Expansion Details:".blue().bold());
        } else {
            println!("   {}", "Details:".red().bold());
        }

        // Output the rendered message with enhanced formatting for diagnostics
        for line in lines {
            if line.trim().is_empty() {
                println!();
                continue;
            }

            // Detect start of expansion
            if line.contains("diagnostics via expansion") {
                println!("   {}", line.blue().bold());
                in_expansion = true;
                continue;
            }

            if is_diagnostic && in_expansion {
                // Enhanced formatting for diagnostic expansion
                if line.trim_start().starts_with("|") {
                    // Extract the code part after the line marker
                    if let Some(pipe_pos) = line.find("|") {
                        let prefix = &line[..pipe_pos + 1];
                        let code_part = &line[pipe_pos + 1..];

                        // Highlight different verification constructs
                        if code_part.contains("==>") {
                            println!("   {}{}", prefix.dimmed(), code_part.yellow().bold());
                        } else if code_part.contains("✔") {
                            println!("   {}{}", prefix.dimmed(), code_part.green().bold());
                        } else if code_part.contains("✘") {
                            println!("   {}{}", prefix.dimmed(), code_part.red().bold());
                        } else {
                            println!("   {}{}", prefix.dimmed(), code_part.white());
                        }
                    } else {
                        println!("   {}", line.white());
                    }
                } else if line.contains("-->") {
                    println!("   {}", line.bright_blue());
                } else if line.starts_with("note:") {
                    println!("   {}", line.blue().bold());
                } else {
                    println!("   {}", line.white());
                }
            } else {
                // Regular formatting for errors
                if line.starts_with("error:") {
                    println!("   {}", line.red().bold());
                } else if line.contains("-->") {
                    println!("   {}", line.bright_blue());
                } else if line.contains("failed precondition")
                    || line.contains("failed this postcondition")
                    || line.contains("assertion failed")
                {
                    println!("   {}", line.red().bold());
                } else if line.trim_start().starts_with("|") {
                    // Code lines - highlight important ones
                    if line.contains("^") || line.contains("~") {
                        println!("   {}", line.red().bold());
                    } else {
                        println!("   {}", line.dimmed());
                    }
                } else {
                    println!("   {}", line);
                }
            }
        }
    }

    fn print_error_summary(&self, rendered: &str, level_color: &str) {
        let lines: Vec<&str> = rendered.lines().collect();

        // Show key lines only
        for line in lines.iter().take(10) {
            if line.contains("-->") {
                println!("   {}", line.bright_blue());
            } else if line.contains("^") || line.contains("~") {
                println!("   {}", line.color(level_color).bold());
            } else if line.starts_with("help:") || line.starts_with("note:") {
                println!("   {}", line.cyan());
                break; // Show first help/note and stop
            }
        }
    }

    fn print_manual_formatting(&self, msg: &CompilerMessage, _level_color: &str) {
        // Print primary spans with file information
        for span in &msg.spans {
            if span.is_primary {
                println!(
                    "   {} {}:{}:{}",
                    "→".bright_blue(),
                    span.file_name.bright_white(),
                    span.line_start.to_string().bright_white(),
                    span.column_start.to_string().bright_white()
                );

                // Print first few lines of code context
                for text in span.text.iter().take(2) {
                    let line = &text.text;
                    if !line.trim().is_empty() {
                        println!("     {}", line.dimmed());
                    }
                }

                if let Some(label) = &span.label {
                    println!("     {}: {}", "help".cyan(), label.cyan());
                }
                break; // Only show first primary span
            }
        }

        // Print first help message
        for child in &msg.children {
            if child.level == "help" || child.level == "note" {
                println!("   {} {}", child.level.cyan(), child.message.cyan());
                break;
            }
        }
    }
}

// Configuration constants - no user-specific paths
// const DEFAULT_VERUS_REPO: &str = "https://github.com/hiroki-chen/verus.git";
const DEFAULT_MEMORY: &str = "4G";
const DEFAULT_SMP_CORES: u32 = 4;

/// Configuration struct to hold all paths and settings
#[derive(Debug)]
struct ProjectConfig {
    root: PathBuf,
    target_arch: String,
    target_triple: String,
}

impl ProjectConfig {
    fn new(target_arch: String) -> Self {
        let root = project_root();
        let target_triple = format!("x86_64-{}-deko", target_arch);

        ProjectConfig { root, target_arch, target_triple }
    }

    // Helper methods to generate paths dynamically
    fn target_dir(&self, release: bool) -> PathBuf {
        let profile = if release { "release" } else { "debug" };
        self.root.join("target").join(&self.target_triple).join(profile)
    }

    fn stage1_path(&self, release: bool) -> PathBuf {
        let profile = if release { "release" } else { "debug" };
        self.root.join("target").join("x86_64-unknown-uefi").join(profile).join("deko-stage1.efi")
    }

    fn deko_monitor_path(&self, release: bool) -> PathBuf { self.target_dir(release).join("deko") }

    fn stage2_binary_path(&self, release: bool) -> PathBuf {
        self.target_dir(release).join("deko-stage2.bin")
    }

    fn stage2_path(&self, release: bool) -> PathBuf { self.target_dir(release).join("stage2") }

    fn deko_elf_path(&self, release: bool) -> PathBuf { self.target_dir(release).join("deko.elf") }

    fn boot_image_path(&self) -> PathBuf { self.target_dir(false).join("boot.img") }

    fn igvm_path(&self) -> PathBuf { self.target_dir(false).join("igvm.igvm") }

    fn custom_target_json(&self) -> PathBuf {
        self.root.join(".cargo").join(format!("{}.json", self.target_triple))
    }

    fn default_ovmf_path() -> PathBuf {
        // Try multiple common locations
        let possible_paths = vec![
            PathBuf::from("/usr/local/share/ovmf/OVMF.fd"),
            dirs::data_local_dir().map(|d| d.join("share/ovmf/OVMF.fd")).unwrap_or_default(),
            PathBuf::from("/usr/share/ovmf/OVMF_CODE.fd"),
        ];

        for path in possible_paths {
            if path.exists() {
                return path;
            }
        }

        // Fallback to user's home directory
        dirs::home_dir()
            .map(|d| d.join(".local/share/ovmf/OVMF.fd"))
            .unwrap_or_else(|| PathBuf::from("~/.local/share/ovmf/OVMF.fd"))
    }

    fn qemu_config_path(&self) -> PathBuf { self.root.join(".config/qemu.config.toml") }
}

#[derive(Debug)]
struct FinalQemuConfig {
    memory: String,
    smp_cores: u32,
    enable_cvm: bool,
    enable_graphics: bool, // Unified graphic/nographic switch
    drive: Vec<DriveConfig>,
    debug: bool,
    igvm_path: String,
    bios_path: String,
    extra_config: Vec<String>,
}

#[derive(Debug, Deserialize, Clone)]
struct DriveConfig {
    file: PathBuf,
    format: String,
    interface: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct PartialQemuConfig {
    memory: Option<String>,
    smp_cores: Option<u32>,
    enable_cvm: Option<bool>,
    enable_graphics: Option<bool>,
    drive: Option<Vec<DriveConfig>>,
    debug: Option<bool>,
    igvm_path: Option<String>,
    bios_path: Option<String>,
    extra_config: Option<Vec<String>>,
}

#[derive(ValueEnum, Debug, Clone)]
enum BuildTarget {
    Deko,
    Stage1,
    All,
}

#[derive(ValueEnum, Debug, Clone)]
enum TargetArch {
    Tdx,
    Snp,
}
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
    #[arg(short, long, value_enum, global = true)]
    target_arch: Option<TargetArch>,
}

#[derive(Subcommand, Debug)]
enum Commands {
    CreateBootable {
        #[arg(short, long)]
        ovmf_path: Option<PathBuf>,
        #[arg(short, long)]
        stage2_path: Option<PathBuf>,
        #[arg(short, long)]
        stage1_path: Option<PathBuf>,
    },

    Qemu {
        #[arg(short, long)]
        config_path: Option<PathBuf>,
    },

    Build {
        #[arg(short, long, value_enum)]
        target: BuildTarget,
        #[arg(short, long)]
        release: bool,
    },

    Pretty {
        #[arg(short, long)]
        paths: Vec<PathBuf>,
    },

    BootstrapVerus {
        #[arg(short, long)]
        commit: Option<String>,
    },

    BootstrapQemu {
        #[arg(short, long)]
        /// The directory where QEMU will be built and installed
        prefix: PathBuf,
    },
}

impl Default for FinalQemuConfig {
    fn default() -> Self {
        let config = ProjectConfig::new("snp".to_string()); // Default to SNP

        FinalQemuConfig {
            memory: DEFAULT_MEMORY.to_string(),
            smp_cores: DEFAULT_SMP_CORES,
            enable_cvm: true,
            enable_graphics: false,
            drive: vec![],
            igvm_path: config.igvm_path().display().to_string(),
            debug: false,
            bios_path: ProjectConfig::default_ovmf_path().display().to_string(),
            extra_config: vec![],
        }
    }
}

struct Builder {
    config: ProjectConfig,
}
impl Builder {
    pub fn new(target_arch: String) -> Self { Builder { config: ProjectConfig::new(target_arch) } }

    /// Find the verus binary using fallback strategy:
    /// 1. Look if it exists in PATH
    /// 2. If not, check if VERUS_PATH environment variable is set  
    /// 3. If not, check if tools/verus exists
    fn find_verus_binary(&self) -> Result<PathBuf> {
        // First check if verus is in PATH
        if let Ok(output) = Command::new("which").arg("verus").output() {
            if output.status.success() {
                let path_str = String::from_utf8_lossy(&output.stdout);
                if !path_str.is_empty() {
                    println!("✓ Found verus in PATH: {}", path_str.bright_green());
                    return Ok(PathBuf::from(path_str.to_string()));
                }
            }
        }

        // Check VERUS_PATH environment variable
        if let Ok(verus_path) = std::env::var("VERUS_PATH") {
            let path = PathBuf::from(verus_path);
            if path.exists() {
                println!("✓ Found verus via VERUS_PATH: {}", path.display().to_string().bright_green());
                return Ok(path);
            } else {
                println!("⚠ VERUS_PATH set but file doesn't exist: {}", path.display().to_string().yellow());
            }
        }

        // Check tools/verus in project
        let tools_verus = self.config.root.join("tools").join("verus");
        if tools_verus.exists() {
            println!("✓ Found verus in project tools: {}", tools_verus.display().to_string().bright_green());
            return Ok(tools_verus);
        }

        bail!("Could not find verus binary. Please ensure it's in PATH, set VERUS_PATH, or run 'cargo run --bin xtask -- bootstrap-verus' first.");
    }

    /// Find the z3 binary using fallback strategy:
    /// 1. Look if it exists in PATH
    /// 2. If not, check if VERUS_Z3_PATH environment variable is set
    /// 3. If not, check if tools/z3 exists  
    fn find_z3_binary(&self) -> Result<PathBuf> {
        // First check if z3 is in PATH
        if let Ok(output) = Command::new("which").arg("z3").output() {
            if output.status.success() {
                let path_str = String::from_utf8_lossy(&output.stdout);
                if !path_str.is_empty() {
                    println!("✓ Found z3 in PATH: {}", path_str.bright_green());
                    return Ok(PathBuf::from(path_str.to_string()));
                }
            }
        }

        // Check VERUS_Z3_PATH environment variable
        if let Ok(z3_path) = std::env::var("VERUS_Z3_PATH") {
            let path = PathBuf::from(z3_path);
            if path.exists() {
                println!("✓ Found z3 via VERUS_Z3_PATH: {}", path.display().to_string().bright_green());
                return Ok(path);
            } else {
                println!("⚠ VERUS_Z3_PATH set but file doesn't exist: {}", path.display().to_string().yellow());
            }
        }

        // Check tools/z3 in project
        let tools_z3 = self.config.root.join("tools").join("z3");
        if tools_z3.exists() {
            println!("✓ Found z3 in project tools: {}", tools_z3.display().to_string().bright_green());
            return Ok(tools_z3);
        }

        bail!("Could not find z3 binary. Please ensure it's in PATH, set VERUS_Z3_PATH, or run 'cargo run --bin xtask -- bootstrap-verus' first.");
    }

    pub fn build(&self, target: BuildTarget, release: bool) -> Result<()> {
        match target {
            BuildTarget::All => {
                self.build(BuildTarget::Stage1, release)?;
                self.build(BuildTarget::Deko, release)?;
                Ok(())
            }
            BuildTarget::Deko => self.build_deko(release),
            BuildTarget::Stage1 => self.build_stage1(release),
        }
    }

    /// Execute a cargo command with JSON message parsing for better error display
    fn execute_cargo_with_json(&self, mut cmd: Command, log_file_name: &str) -> Result<()> {
        // Enable JSON output for cargo commands
        cmd.args(["--message-format", "json", "--", "--expand-errors"]);
        cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

        let log_dir = self.config.root.join("logs");
        std::fs::create_dir_all(&log_dir).context("Failed to create logs directory")?;

        let log_file_path = log_dir.join(log_file_name);
        let mut log_file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&log_file_path)
            .with_context(|| format!("Failed to create log file: {:?}", log_file_path))?;

        println!("{} Executing command: {:?}", "→".bright_blue(), cmd);
        println!("{} Logs will be written to: {:?}", "📝".bright_cyan(), log_file_path);

        writeln!(log_file, "=== COMMAND ===")?;
        writeln!(log_file, "{:?}", cmd)?;
        writeln!(log_file, "\n=== OUTPUT ===")?;

        let mut child = cmd.spawn().context("Failed to spawn command")?;
        let stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();

        let mut summary = BuildSummary::default();
        let mut progress_count = 0;

        // Parse stdout for JSON messages
        let stdout_reader = BufReader::new(stdout);
        for line in stdout_reader.lines() {
            let line = line.context("Failed to read stdout line")?;
            writeln!(log_file, "{}", line)?;

            // Try to parse as JSON cargo message
            if let Ok(msg) = serde_json::from_str::<CargoMessage>(&line) {
                match msg {
                    CargoMessage::CompilerMessage { message } => {
                        summary.add_message(message);
                    }
                    CargoMessage::BuildFinished { success } => {
                        summary.successful = success;
                    }
                    CargoMessage::Other => {
                        // Could be a progress message, show some progress
                        progress_count += 1;
                        if progress_count % 10 == 0 {
                            print!(".");
                            std::io::stdout().flush().unwrap_or(());
                        }
                    }
                }
            } else {
                // Non-JSON output, just show it
                if !line.trim().is_empty() {
                    println!("{}", line);
                }
            }
        }

        // Read stderr
        let stderr_reader = BufReader::new(stderr);
        for line in stderr_reader.lines() {
            let line = line.context("Failed to read stderr line")?;
            writeln!(log_file, "STDERR: {}", line)?;
            if !line.trim().is_empty() {
                println!("{} {}", "stderr:".red(), line);
            }
        }

        let status = child.wait().context("Failed to wait for command")?;
        writeln!(log_file, "\n=== EXIT STATUS ===")?;
        writeln!(log_file, "{}", status)?;

        // Print summary
        summary.print_summary();

        if !status.success() {
            return Err(anyhow::anyhow!("Command failed with exit code: {}", status));
        }

        Ok(())
    }

    /// Execute a regular command (non-cargo) with logging
    fn execute_with_logging(&self, mut cmd: Command, log_file_name: &str) -> Result<()> {
        let log_dir = self.config.root.join("logs");
        std::fs::create_dir_all(&log_dir).context("Failed to create logs directory")?;

        let log_file_path = log_dir.join(log_file_name);
        let log_file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&log_file_path)
            .with_context(|| format!("Failed to create log file: {:?}", log_file_path))?;

        println!("{} Executing command: {:?}", "→".bright_blue(), cmd);
        println!("{} Logs will be written to: {:?}", "📝".bright_cyan(), log_file_path);

        let output = cmd.output().context("Failed to execute command")?;

        // Write both stdout and stderr to the log file
        let mut log_file = log_file;
        writeln!(log_file, "=== COMMAND ===")?;
        writeln!(log_file, "{:?}", cmd)?;
        writeln!(log_file, "\n=== STDOUT ===")?;
        log_file.write_all(&output.stdout)?;
        writeln!(log_file, "\n=== STDERR ===")?;
        log_file.write_all(&output.stderr)?;
        writeln!(log_file, "\n=== EXIT STATUS ===")?;
        writeln!(log_file, "{}", output.status)?;

        // Also print a summary to console
        if !output.status.success() {
            println!("{} Command failed with exit code: {}", "✗".red(), output.status);
            println!("{} Check log file for details: {:?}", "📄".yellow(), log_file_path);

            // Print last few lines of stderr for immediate feedback
            let stderr_str = String::from_utf8_lossy(&output.stderr);
            let stderr_lines: Vec<&str> = stderr_str.lines().collect();
            if !stderr_lines.is_empty() {
                println!("{}", "Last few lines of stderr:".yellow());
                for line in stderr_lines.iter().rev().take(5).rev() {
                    println!("  {}", line);
                }
            }

            return Err(anyhow::anyhow!("Command failed"));
        } else {
            println!("{} Command completed successfully", "✓".green());

            // Print last few lines of stdout for immediate feedback
            let stdout_str = String::from_utf8_lossy(&output.stdout);
            let stdout_lines: Vec<&str> = stdout_str.lines().collect();
            if !stdout_lines.is_empty() {
                println!("{}", "Last few lines of output:".cyan());
                for line in stdout_lines.iter().rev().take(3).rev() {
                    if !line.trim().is_empty() {
                        println!("  {}", line);
                    }
                }
            }
        }

        Ok(())
    }

    fn build_deko(&self, release: bool) -> Result<()> {
        println!("{}", "--- Building stage2 bootloader ---".bright_cyan().bold());

        // Discover required binaries
        println!("\n{} Discovering required binaries...", "🔍".bright_yellow());
        let verus_binary = self.find_verus_binary()?;
        let z3_binary = self.find_z3_binary()?;

        // Set up environment for verus
        std::env::set_var("VERUS_Z3_PATH", &z3_binary);
        
        let deko_stage2 = self.config.root.join("deko-core");
        std::env::set_current_dir(&deko_stage2)
            .context("Failed to change directory to deko-core")?;

        // Build stage2 using discovered verus binary
        let mut cmd = Command::new("cargo");
        // Set the verus binary path in PATH or use custom cargo subcommand
        if verus_binary != PathBuf::from("verus") {
            // If verus is not in PATH, we need to set up the environment
            let verus_dir = verus_binary.parent().unwrap_or_else(|| Path::new("."));
            let current_path = std::env::var("PATH").unwrap_or_default();
            let new_path = format!("{}:{}", verus_dir.display(), current_path);
            std::env::set_var("PATH", new_path);
        }
        
        cmd.arg("verus")
            .arg("build")
            .arg("--target")
            .arg(self.config.custom_target_json())
            .arg("--features")
            .arg(&self.config.target_arch)
            .arg("--bin")
            .arg("stage2");

        if release {
            cmd.arg("--release");
        }

        let profile = if release { "release" } else { "debug" };
        let log_file = format!("deko-stage2-build-{}-{}.log", self.config.target_arch, profile);
        self.execute_cargo_with_json(cmd, &log_file)?;

        // Create flat image for SNP
        if self.config.target_arch == "snp" {
            let mut cmd = Command::new("objcopy");
            cmd.arg("-O")
                .arg("binary")
                .arg(self.config.stage2_path(release))
                .arg(self.config.stage2_binary_path(release));

            let log_file =
                format!("deko-stage2-objcopy-{}-{}.log", self.config.target_arch, profile);
            self.execute_with_logging(cmd, &log_file)?;
        }

        println!("{}", "--- Building Deko Monitor ---".bright_cyan().bold());

        // Build monitor
        let mut cmd = Command::new("cargo");
        cmd.arg("verus")
            .arg("build")
            .arg("--target")
            .arg(self.config.custom_target_json())
            .arg("--features")
            .arg(&self.config.target_arch)
            .arg("--bin")
            .arg("deko");

        if release {
            cmd.arg("--release");
        }

        let log_file = format!("deko-monitor-build-{}-{}.log", self.config.target_arch, profile);
        self.execute_cargo_with_json(cmd, &log_file)?;

        // Create ELF for SNP
        if self.config.target_arch == "snp" {
            let mut cmd = Command::new("objcopy");
            cmd.arg("-O")
                .arg("elf64-x86-64")
                .arg("--strip-unneeded")
                .arg(self.config.deko_monitor_path(release))
                .arg(self.config.deko_elf_path(release));

            let log_file =
                format!("deko-monitor-objcopy-{}-{}.log", self.config.target_arch, profile);
            self.execute_with_logging(cmd, &log_file)?;
        }

        Ok(())
    }

    fn build_stage1(&self, release: bool) -> Result<()> {
        println!("{}", "--- Building stage1 bootloader ---".bright_cyan().bold());

        let mut cmd = Command::new("cargo");
        cmd.arg("build")
            .arg("--package")
            .arg("deko-stage1")
            .arg("--target")
            .arg("x86_64-unknown-uefi")
            .arg("--features")
            .arg(&self.config.target_arch);

        if release {
            cmd.arg("--release");
        }

        let profile = if release { "release" } else { "debug" };
        let log_file = format!("deko-stage1-build-{}-{}.log", self.config.target_arch, profile);
        self.execute_cargo_with_json(cmd, &log_file)?;

        Ok(())
    }

    pub fn qemu(&self, config_path: Option<PathBuf>) -> Result<()> {
        let config_path = config_path.unwrap_or_else(|| self.config.qemu_config_path());

        let config = match load_qemu_config(&config_path) {
            Ok(cfg) => cfg,
            Err(e) => {
                println!("Warning: Failed to load config ({}), using defaults", e);
                Default::default()
            }
        };

        println!("✓ Launching QEMU");
        println!("Configuration: {:#?}", config);

        let mut cmd = std::process::Command::new("qemu-system-x86_64");
        cmd.args(["-accel", "kvm", "-cpu", "host"]);
        cmd.arg("-smp").arg(config.smp_cores.to_string());

        // Add drives
        for (i, drive) in config.drive.iter().enumerate() {
            cmd.arg("-drive").arg(format!(
                "file={},if={},format={},id=disk{}",
                drive.file.display(),
                drive.interface,
                drive.format,
                i
            ));
        }

        // Graphics configuration
        if !config.enable_graphics {
            cmd.args(["-nographic", "-vga", "none"]);
        }

        // Low-level machine and serial config
        cmd.args(["-serial", "stdio", "-nodefaults", "-no-reboot"]);

        if config.enable_cvm {
            match self.config.target_arch.as_str() {
                "snp" => qemu_sev(&config, &mut cmd),
                "tdx" => qemu_tdx(&config, &mut cmd),
                _ => bail!("Unsupported target architecture: {}", self.config.target_arch),
            }
        }

        if config.debug {
            cmd.arg("-s");
            println!("✓ Debugging mode enabled: QEMU will start with GDB server on port 1234");
        }

        if !config.extra_config.is_empty() {
            println!("✓ Adding extra QEMU configurations: {:?}", config.extra_config);
            for extra in &config.extra_config {
                let parts: Vec<&str> = extra.split_whitespace().collect();
                cmd.args(&parts);
            }
        }

        println!("✓ Executing command: {:?}", cmd);

        let mut child = cmd.spawn().context("Failed to spawn QEMU")?;
        child.wait().context("QEMU process failed")?;

        Ok(())
    }

    pub fn create_bootable(
        &self,
        ovmf_path: Option<PathBuf>,
        stage2_path: Option<PathBuf>,
        stage1_path: Option<PathBuf>,
    ) -> Result<()> {
        match self.config.target_arch.as_str() {
            "snp" => self.create_bootable_snp(ovmf_path, stage2_path),
            "tdx" => self.create_bootable_tdx(stage2_path, stage1_path),
            _ => bail!("Unsupported target architecture: {}", self.config.target_arch),
        }
    }

    fn create_bootable_tdx(
        &self,
        deko_monitor_path: Option<PathBuf>,
        stage1_path: Option<PathBuf>,
    ) -> Result<()> {
        // Build everything first
        self.build(BuildTarget::All, true)?;

        let loader_path = stage1_path.unwrap_or_else(|| self.config.stage1_path(true));
        let deko_monitor_path =
            deko_monitor_path.unwrap_or_else(|| self.config.deko_monitor_path(true));
        let boot_img_path = self.config.boot_image_path();

        println!("✓ Creating bootable image with:");
        println!("  Loader Path: {:?}", loader_path);
        println!("  Deko Monitor Path: {:?}", deko_monitor_path);
        println!("  Boot Image Path: {:?}", boot_img_path);

        // Create boot image
        let img_file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(&boot_img_path)
            .context("Failed to create or open boot image file")?;

        let img_len = 1024 * 1024 * 64; // 64 MB
        img_file.set_len(img_len)?;

        let format_options = fatfs::FormatVolumeOptions::new();
        fatfs::format_volume(&img_file, format_options)?;

        let fs = fatfs::FileSystem::new(&img_file, fatfs::FsOptions::new())?;
        let root_dir = fs.root_dir();
        let efi_dir = root_dir.create_dir("EFI")?;
        let boot_dir = efi_dir.create_dir("BOOT")?;

        let mut dest_file = boot_dir.create_file("BOOTX64.EFI")?;
        dest_file.truncate()?;
        std::io::copy(&mut fs::File::open(&loader_path)?, &mut dest_file)?;

        let mut dest_file = root_dir.create_file("deko.bin")?;
        dest_file.truncate()?;
        std::io::copy(&mut fs::File::open(&deko_monitor_path)?, &mut dest_file)?;

        println!("✓ Boot Image created at {:?}", boot_img_path);
        Ok(())
    }

    fn create_bootable_snp(
        &self,
        ovmf_path: Option<PathBuf>,
        stage2_path: Option<PathBuf>,
    ) -> Result<()> {
        // Build everything first
        // self.build(BuildTarget::Deko, true)?;

        let stage2_path = stage2_path.unwrap_or_else(|| self.config.stage2_binary_path(true));
        let boot_img_path = self.config.igvm_path();
        let ovmf_path = ovmf_path.unwrap_or_else(ProjectConfig::default_ovmf_path);
        let kernel_path = self.config.deko_monitor_path(false);

        println!("✓ Creating IGVM image with:");
        println!("  Stage2 Path: {:?}", stage2_path);
        println!("  Kernel Path: {:?}", kernel_path);
        println!("  OVMF Path: {:?}", ovmf_path);
        println!("  Output: {:?}", boot_img_path);

        let mut cmd = std::process::Command::new("igvmbuilder");
        cmd.args(["--sort", "--policy", "0x30000", "--snp"]);
        cmd.args(["--firmware", &ovmf_path.display().to_string()]);
        cmd.args(["--stage2", &stage2_path.display().to_string()]);
        cmd.args(["--kernel", &kernel_path.display().to_string()]);
        cmd.args(["--output", &boot_img_path.display().to_string()]);
        cmd.arg("qemu");

        // Change directory back to project root
        std::env::set_current_dir(&self.config.root)
            .context("Failed to change directory to project root")?;

        println!("✓ Executing command: {:?}", cmd);

        if !cmd.status()?.success() {
            bail!("igvmbuilder failed");
        }

        println!("✓ IGVM Image created at {:?}", boot_img_path);
        Ok(())
    }
}

fn qemu_sev(config: &FinalQemuConfig, cmd: &mut std::process::Command) {
    cmd.arg("-machine").arg(
        "type=q35,confidential-guest-support=sev,kernel_irqchip=split,igvm-cfg=igvm,memory-backend=ram"
    );
    cmd.args(["-object", "sev-snp-guest,id=sev,reduced-phys-bits=1,cbitpos=51"]);
    cmd.arg("-object").arg(format!("memory-backend-memfd,id=ram,size={}", config.memory));
    cmd.arg("-object").arg(format!("igvm-cfg,id=igvm,file={}", config.igvm_path));
}

fn qemu_tdx(config: &FinalQemuConfig, cmd: &mut std::process::Command) {
    cmd.arg("-machine")
        .arg("type=q35,confidential-guest-support=tdx,kernel_irqchip=split,memory-backend=ram0");

    let tdx_arg = if config.debug { "tdx-guest,id=tdx,debug=on" } else { "tdx-guest,id=tdx" };

    cmd.args(["-object", tdx_arg]);
    cmd.args(["-object", "iommufd,id=iommufd0"]);
    cmd.arg("-object").arg(format!("memory-backend-ram,id=ram0,size={}", config.memory));
    cmd.args(["-bios", &config.bios_path]);
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let target_arch = match cli.target_arch.unwrap_or(TargetArch::Tdx) {
        TargetArch::Tdx => "tdx",
        TargetArch::Snp => "snp",
    };

    let builder = Builder::new(target_arch.to_string());

    match cli.command {
        Commands::CreateBootable { ovmf_path, stage2_path, stage1_path } => {
            builder.create_bootable(ovmf_path, stage2_path, stage1_path)
        }

        Commands::Qemu { config_path } => builder.qemu(config_path),

        Commands::Build { target, release } => builder.build(target, release),

        Commands::Pretty { paths } => pretty(paths),

        Commands::BootstrapVerus { commit } => {
            let default_prefix = project_root().join("/tmp");
            bootstrap_verus(&default_prefix, commit.as_deref())
        }

        Commands::BootstrapQemu { prefix } => bootstrap_qemu(&prefix),
    }
}

fn bootstrap_qemu(prefix: &Path) -> Result<()> {
    println!("Bootstrapping QEMU with IGVM support...");
    println!("Installation prefix: {}", prefix.display());

    // Ensure prefix directory exists
    std::fs::create_dir_all(prefix).context("Failed to create prefix directory")?;

    // Step 2: Clone and build QEMU with IGVM support
    println!("\n--- Building QEMU with IGVM support ---");
    let qemu_dir = prefix.join("qemu");

    if !qemu_dir.exists() {
        println!("Cloning QEMU repository...");
        let repo = Repository::clone("https://github.com/coconut-svsm/qemu", &qemu_dir)
            .context("Failed to clone QEMU repository")?;

        // Checkout the svsm-igvm branch
        println!("Checking out svsm-igvm branch...");

        let branch_name = "svsm-igvm";
        let (object, reference) = repo
            .revparse_ext(branch_name)
            .with_context(|| format!("Failed to find branch {}", branch_name))?;
        repo.checkout_tree(&object, None)?;
        repo.set_head(reference.unwrap().name().unwrap())?;

        println!("✓ Checked out branch: {}", branch_name);
    } else {
        println!("QEMU repository already exists at {:?}", qemu_dir);

        // Ensure we're on the right branch
        let repo = Repository::open(&qemu_dir)?;
        let head = repo.head()?;
        let current_branch = head.shorthand().unwrap_or("unknown");

        if current_branch != "svsm-igvm" {
            println!("Switching to svsm-igvm branch...");
            repo.set_head("refs/heads/svsm-igvm")?;
            repo.checkout_head(Some(git2::build::CheckoutBuilder::default().force()))?;
        }
    }

    // Configure QEMU
    std::env::set_current_dir(&qemu_dir).context("Failed to change directory to QEMU repo")?;

    let qemu_install_dir = prefix.join("qemu-svsm");
    println!("Configuring QEMU...");
    println!("  Install directory: {:?}", qemu_install_dir);

    let mut cmd = std::process::Command::new("./configure");
    cmd.arg(format!("--prefix={}", qemu_install_dir.display()))
        .arg("--target-list=x86_64-softmmu")
        .arg("--enable-igvm");

    println!("Running: {:?}", cmd);
    let output = cmd.output().context("Failed to configure QEMU")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);

        // Check for common issues
        if stderr.contains("igvm") || stdout.contains("igvm") {
            eprintln!(
                "IGVM library might not be properly installed. Make sure ldconfig has been run."
            );
            eprintln!("You may need to run: sudo ldconfig");
        }

        bail!("Failed to configure QEMU:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }
    println!("✓ QEMU configured successfully");

    // Build QEMU with ninja
    println!("Building QEMU with ninja...");
    let mut cmd = std::process::Command::new("ninja");
    cmd.arg("-C").arg("build/");

    println!("This may take several minutes...");
    let output = cmd.output().context("Failed to build QEMU with ninja")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Failed to build QEMU:\n{}", stderr);
    }
    println!("✓ QEMU built successfully");

    // Install QEMU
    println!("Installing QEMU...");
    let mut cmd = std::process::Command::new("make");
    cmd.arg("install");

    let output = cmd.output().context("Failed to install QEMU")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Failed to install QEMU:\n{}", stderr);
    }

    println!("✓ QEMU installed successfully");

    // Print final instructions
    println!("\n=== QEMU with IGVM support installed successfully! ===");
    println!("QEMU binary location: {:?}", qemu_install_dir.join("bin/qemu-system-x86_64"));
    println!("\nTo use this QEMU, add it to your PATH:");
    println!("  export PATH={}:$PATH", qemu_install_dir.join("bin").display());
    println!("\nOr use the full path when running QEMU:");
    println!("  {}/qemu-system-x86_64 [options]", qemu_install_dir.join("bin").display());

    Ok(())
}

fn bootstrap_verus(prefix: &Path, commit: Option<&str>) -> Result<()> {
    println!("{} Bootstrapping Verus from source...", "→".bright_cyan());
    println!("Installation prefix: {}", prefix.display().to_string().bright_white());

    // Ensure prefix directory exists
    std::fs::create_dir_all(prefix).context("Failed to create prefix directory")?;

    let verus_dir = prefix.join("verus");

    // Step 1: Clone or update Verus repository
    println!("\n{} Cloning Verus repository...", "🔀".bright_yellow());

    if verus_dir.exists() {
        println!("🗑 Removing existing verus directory...");
        std::fs::remove_dir_all(&verus_dir).context("Failed to remove existing verus directory")?;
    }

    let repo_url = "https://github.com/verus-lang/verus.git";
    println!("Cloning from: {}", repo_url.bright_blue());

    let repo =
        Repository::clone(repo_url, &verus_dir).context("Failed to clone Verus repository")?;

    // Checkout specific commit if provided
    if let Some(commit_hash) = commit {
        println!("Checking out commit: {}", commit_hash.bright_yellow());
        let (object, _) = repo
            .revparse_ext(commit_hash)
            .with_context(|| format!("Failed to find commit {}", commit_hash))?;
        repo.checkout_tree(&object, None).context("Failed to checkout commit")?;
        repo.set_head_detached(object.id()).context("Failed to set HEAD to commit")?;
    }

    println!("✓ Repository cloned successfully!");

    // Enter the verus directory
    std::env::set_current_dir(&verus_dir).context("Failed to change to verus directory")?;
    println!("✓ Changed to verus directory: {}", verus_dir.display().to_string().bright_white());
    let rust_toolchain = std::fs::read_to_string(verus_dir.join("rust-toolchain.toml"))
        .context("Failed to read rust-toolchain file")?
        .split("\n")
        .map(|s| s.to_string())
        .collect::<Vec<String>>();
    let rust_version = rust_toolchain
        .iter()
        .find(|line| line.trim_start().starts_with("channel"))
        .and_then(|line| line.split('=').nth(1))
        .map(|s| s.trim().trim_matches('"'))
        .unwrap_or("stable");
    println!("{} Setting Rust toolchain to: {}", "🛠".bright_green(), rust_version.bright_white());

    let mut cmd = Command::new("rustup");
    cmd.arg("override").arg("set").arg(rust_version);
    let output = cmd.output().context("Failed to set rustup override")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("rustup override failed:\nSTDERR:\n{}", stderr);
    }

    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
    let output = cmd.output().context("Failed to check rustup version")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("rustup check failed:\nSTDERR:\n{}", stderr);
    }

    // Step 2: Change to source directory
    let source_dir = verus_dir.join("source");
    if !source_dir.exists() {
        bail!("Source directory not found at: {:?}", source_dir);
    }

    println!("\n{} Changing to source directory: {}", "📂".bright_cyan(), source_dir.display());
    std::env::set_current_dir(&source_dir).context("Failed to change to source directory")?;

    // Step 3: Setup Z3
    println!("\n{} Setting up Z3...", "🔧".bright_green());

    let mut cmd = Command::new("bash");
    cmd.arg("./tools/get-z3.sh");
    println!("Running: {:?}", cmd);

    let output = cmd.output().context("Failed to execute get-z3.sh")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("get-z3.sh failed:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }

    println!("✓ Z3 setup completed successfully!");

    // Step 4: Check for rustup
    println!("\n{} Checking rustup installation...", "🦀".bright_yellow());
    let rustup_check = Command::new("rustup").arg("--version").output();

    match rustup_check {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("✓ Found rustup: {}", version.trim().bright_white());
        }
        _ => {
            bail!("rustup not found. Please install rustup from https://rustup.rs first.");
        }
    }

    println!("✓ rustup is installed.");

    // Step 5: Build vargo
    println!("\n{} Building vargo... ", "⚙️".bright_green());
    let vargo_dir = verus_dir.join("tools/vargo");
    std::env::set_current_dir(&vargo_dir).context("Failed to change to vargo directory")?;
    let mut cmd = Command::new("cargo");
    cmd.arg("build").arg("--release");
    println!("Running: {:?}", cmd);
    let output = cmd.output().context("Failed to build vargo")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("Failed to build vargo:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }

    let vargo_binary = vargo_dir.join("target/release/vargo");

    // Step 6: build verus.
    println!("\n{} Building Verus using vargo...", "🚀".bright_green());
    // unset RUSTUP_TOOLCHAIN.
    std::env::remove_var("RUSTUP_TOOLCHAIN");
    std::env::set_current_dir(&source_dir).context("Failed to change to source directory")?;
    let mut cmd = Command::new(&vargo_binary);
    cmd.arg("build").arg("--release");
    println!("Running: {:?} at {}", cmd, source_dir.display());
    let output = cmd.output().context("Failed to build Verus using vargo")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("Failed to build Verus:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }

    println!("✓ Verus built successfully!");

    // Step 7: Copy all built files from /tmp/verus/source/target/release to tools directory
    println!("\n{} Copying Verus binaries to project tools directory...", "📦".bright_cyan());
    
    let verus_target_path = source_dir.join("target/release");
    let project_tools_dir = project_root().join("tools");
    
    println!("Source directory: {}", verus_target_path.display().to_string().bright_white());
    println!("Destination directory: {}", project_tools_dir.display().to_string().bright_white());
    
    // Ensure destination directory exists
    std::fs::create_dir_all(&project_tools_dir).context("Failed to create tools directory")?;
    
    // Copy all files from target/release to tools
    copy_dir_recursive(&verus_target_path, &project_tools_dir)
        .context("Failed to copy Verus built files to tools directory")?;
    
    // Also copy z3 binary
    let z3_path = source_dir.join("z3");
    if z3_path.exists() {
        println!("Copying Z3 binary...");
        let z3_dest = project_tools_dir.join("z3");
        std::fs::copy(&z3_path, &z3_dest).context("Failed to copy Z3 binary")?;
        
        // Make Z3 executable
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = std::fs::metadata(&z3_dest)?.permissions();
            perms.set_mode(perms.mode() | 0o755);
            std::fs::set_permissions(&z3_dest, perms)?;
        }
        
        println!("✓ Z3 binary copied and made executable at: {}", z3_dest.display());
    }
    
    println!("✓ All Verus files copied successfully to tools directory!");

    // Step 8: Clean up temporary build directory and create verusroot marker file
    println!("\n{} Finalizing bootstrap setup...", "🔧".bright_cyan());
    
    // Delete the temporary /tmp/verus build directory
    if verus_dir.exists() {
        std::fs::remove_dir_all(&verus_dir).context("Failed to delete temporary verus build directory")?;
        println!("✓ Deleted temporary build directory: {}", verus_dir.display());
    }
    
    // Create empty verusroot marker file
    let verusroot_file = project_tools_dir.join("verus-root");
    std::fs::File::create(&verusroot_file).context("Failed to create verus-root marker file")?;
    println!("✓ Created verusroot marker file at: {}", verusroot_file.display());

    println!("\n=== Verus bootstrap completed successfully! ===");

    Ok(())
}

fn pretty(paths: Vec<PathBuf>) -> Result<()> {
    let root = project_root();

    // If specific paths provided, use those; otherwise find all
    let rs_files = if !paths.is_empty() {
        paths
    } else {
        let mut files = vec![];
        for entry in walkdir::WalkDir::new(&root) {
            let entry = entry?;
            let path = entry.path();

            if entry.file_type().is_file()
                && path.extension().and_then(|s| s.to_str()) == Some("rs")
                && path.to_str().map_or(false, |s| {
                    s.contains("deko") && !s.contains("target") && !s.contains("deko-macros")
                })
            {
                files.push(path.to_path_buf());
            }
        }
        files
    };

    rs_files.par_iter().for_each(|file| {
        let mut cmd = std::process::Command::new("verusfmt");
        let _ = cmd.arg(&file).output();
    });

    println!("✓ Formatted {} files", rs_files.len());
    Ok(())
}

fn load_qemu_config(path: &Path) -> Result<FinalQemuConfig> {
    let mut config = FinalQemuConfig::default();

    if !path.exists() {
        return Err(anyhow::anyhow!("Config file not found: {:?}", path));
    }

    println!("✓ Loading QEMU configuration from: {:?}", path);

    let content = fs::read_to_string(path)?;
    let partial = toml::from_str::<PartialQemuConfig>(&content)?;

    // Apply partial config over defaults
    if let Some(mem) = partial.memory {
        config.memory = mem;
    }
    if let Some(smp) = partial.smp_cores {
        config.smp_cores = smp;
    }
    if let Some(cvm) = partial.enable_cvm {
        config.enable_cvm = cvm;
    }
    if let Some(bios_path) = partial.bios_path {
        config.bios_path = bios_path;
    }
    if let Some(graphics) = partial.enable_graphics {
        config.enable_graphics = graphics;
    }
    if let Some(igvm_path) = partial.igvm_path {
        config.igvm_path = igvm_path;
    }
    if let Some(drive) = partial.drive {
        config.drive = drive;
    }
    if let Some(debug) = partial.debug {
        config.debug = debug;
    }
    if let Some(extra) = partial.extra_config {
        config.extra_config = extra;
    }

    Ok(config)
}

fn copy_dir_recursive(src: &Path, dst: &Path) -> Result<()> {
    std::fs::create_dir_all(dst)?;

    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());

        if file_type.is_dir() {
            copy_dir_recursive(&src_path, &dst_path)?;
        } else {
            std::fs::copy(&src_path, &dst_path)?;
        }
    }

    Ok(())
}

fn project_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).ancestors().nth(1).unwrap().to_path_buf()
}
