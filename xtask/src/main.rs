use std::fs::{self, OpenOptions};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context, Result};
use clap::{Parser, Subcommand, ValueEnum};
use colored::Colorize;
use git2::Repository;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use serde::Deserialize;

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
            PathBuf::from("./tools/share/OVMF.fd"),
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

    Test {
        #[arg(
            help = "Test suite to run (e.g., 'buddy', 'elf'). If not specified, runs all tests."
        )]
        suite: Option<String>,
        #[arg(short, long, help = "Run tests in release mode")]
        release: bool,
    },

    Pretty {
        #[arg(short, long)]
        paths: Vec<PathBuf>,
    },

    BootstrapVerus {
        #[arg(short, long)]
        commit: Option<String>,
        #[arg(short, long)]
        branch: Option<String>,
    },

    BootstrapQemu,

    BootstrapOvmf,

    LineCount,
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
                println!(
                    "✓ Found verus via VERUS_PATH: {}",
                    path.display().to_string().bright_green()
                );
                return Ok(path);
            } else {
                println!(
                    "⚠ VERUS_PATH set but file doesn't exist: {}",
                    path.display().to_string().yellow()
                );
            }
        }

        // Check tools/verus in project
        let tools_verus = self.config.root.join("tools").join("verus");
        if tools_verus.exists() {
            println!(
                "✓ Found verus in project tools: {}",
                tools_verus.display().to_string().bright_green()
            );
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
                println!(
                    "✓ Found z3 via VERUS_Z3_PATH: {}",
                    path.display().to_string().bright_green()
                );
                return Ok(path);
            } else {
                println!(
                    "⚠ VERUS_Z3_PATH set but file doesn't exist: {}",
                    path.display().to_string().yellow()
                );
            }
        }

        // Check tools/z3 in project
        let tools_z3 = self.config.root.join("tools").join("z3");
        if tools_z3.exists() {
            println!(
                "✓ Found z3 in project tools: {}",
                tools_z3.display().to_string().bright_green()
            );
            return Ok(tools_z3);
        }

        bail!("Could not find z3 binary. Please ensure it's in PATH, set VERUS_Z3_PATH, or run 'cargo run --bin xtask -- bootstrap-verus' first.");
    }

    /// Find the QEMU binary using fallback strategy:
    /// 1. Check if QEMU_BIN environment variable is set (highest priority)
    /// 2. If not, check if tools/bin/qemu-system-x86_64 exists
    /// 3. Fallback to qemu-system-x86_64 in PATH
    fn find_qemu_binary(&self) -> Result<PathBuf> {
        // Check QEMU_BIN environment variable first (highest priority)
        if let Ok(qemu_path) = std::env::var("QEMU_BIN") {
            let path = PathBuf::from(qemu_path);
            if path.exists() {
                println!(
                    "✓ Found QEMU via QEMU_BIN: {}",
                    path.display().to_string().bright_green()
                );
                return Ok(path);
            } else {
                println!(
                    "⚠ QEMU_BIN set but file doesn't exist: {}",
                    path.display().to_string().yellow()
                );
            }
        }

        // Check tools/bin/qemu-system-x86_64 in project
        let tools_qemu = self.config.root.join("tools").join("bin").join("qemu-system-x86_64");
        if tools_qemu.exists() {
            println!(
                "✓ Found QEMU in project tools: {}",
                tools_qemu.display().to_string().bright_green()
            );
            return Ok(tools_qemu);
        }

        // Fallback to qemu-system-x86_64 in PATH
        println!("✓ Using QEMU from PATH: qemu-system-x86_64");
        Ok(PathBuf::from("qemu-system-x86_64"))
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

    /// Execute a cargo command - simplified version that just runs normally
    fn execute_cargo_with_json(&self, mut cmd: Command, _log_file_name: &str) -> Result<()> {
        println!("{} Executing command: {:?}", "→".bright_blue(), cmd);

        // Run the command normally - no redirection, no JSON parsing, just let it run
        let status = cmd.status().context("Failed to execute command")?;

        if !status.success() {
            return Err(anyhow::anyhow!("Command failed with exit code: {}", status));
        }

        println!("{} Command completed successfully", "✓".green());
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
        std::env::set_var("RUSTC_BOOTSTRAP", "1");

        // let deko_stage2 = self.config.root.join("deko-core");
        // std::env::set_current_dir(&deko_stage2)
        //     .context("Failed to change directory to deko-core")?;
        let stage2_path = self.config.root.join("bin").join("deko-stage2");
        std::env::set_current_dir(&stage2_path)
            .context("Failed to change directory to bin directory")?;

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
            .arg("--")
            .arg("--expand-errors");

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

        let deko_path = self.config.root.join("bin").join("deko-monitor");
        std::env::set_current_dir(&deko_path)
            .context("Failed to change directory to deko-monitor bin directory")?;

        // Build monitor
        let mut cmd = Command::new("cargo");
        cmd.arg("verus")
            .arg("build")
            .arg("--target")
            .arg(self.config.custom_target_json())
            .arg("--features")
            .arg(&self.config.target_arch)
            .arg("--")
            .arg("--expand-errors");

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

        // Find QEMU binary using priority: QEMU_BIN > tools/bin > PATH
        let qemu_binary = self.find_qemu_binary()?;
        let mut cmd = std::process::Command::new(qemu_binary);

        // Set LD_LIBRARY_PATH to include tools/lib directories for IGVM library
        let tools_lib = self.config.root.join("tools").join("lib");
        let tools_lib_arch = tools_lib.join("x86_64-linux-gnu");
        let current_ld_path = std::env::var("LD_LIBRARY_PATH").unwrap_or_default();

        let mut lib_paths = Vec::new();
        if tools_lib_arch.exists() {
            lib_paths.push(tools_lib_arch.display().to_string());
        }
        if tools_lib.exists() {
            lib_paths.push(tools_lib.display().to_string());
        }

        if !lib_paths.is_empty() {
            let new_ld_path = if current_ld_path.is_empty() {
                lib_paths.join(":")
            } else {
                format!("{}:{}", lib_paths.join(":"), current_ld_path)
            };
            cmd.env("LD_LIBRARY_PATH", &new_ld_path);
            println!("✓ Set LD_LIBRARY_PATH={}", new_ld_path);
        }

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

        Commands::Test { suite, release } => test_runner(suite, release),

        Commands::Pretty { paths } => pretty(paths),

        Commands::BootstrapVerus { commit, branch } => {
            let default_prefix = project_root().join("/tmp");
            bootstrap_verus(&default_prefix, commit.as_deref(), branch.as_deref())
        }

        Commands::BootstrapQemu => bootstrap_qemu(),

        Commands::BootstrapOvmf => bootstrap_ovmf(),

        Commands::LineCount => line_count(),
    }
}

fn test_runner(suite: Option<String>, release: bool) -> Result<()> {
    println!("{} Deko Test Runner", "🧪".bright_cyan().bold());

    let project_root = project_root();
    let tests_dir = project_root.join("tests");

    if !tests_dir.exists() {
        bail!("Tests directory not found at: {:?}", tests_dir);
    }

    // Discover available test suites
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

    // Set up environment for verus
    let builder = Builder::new("snp".to_string()); // Use SNP as default for testing
    let verus_binary = builder.find_verus_binary()?;
    let z3_binary = builder.find_z3_binary()?;

    std::env::set_var("VERUS_Z3_PATH", &z3_binary);
    if verus_binary != PathBuf::from("verus") {
        let verus_dir = verus_binary.parent().unwrap_or_else(|| Path::new("."));
        let current_path = std::env::var("PATH").unwrap_or_default();
        let new_path = format!("{}:{}", verus_dir.display(), current_path);
        std::env::set_var("PATH", new_path);
    }

    let mut all_passed = true;

    // Change back to project root for cargo commands
    std::env::set_current_dir(&project_root)?;

    for suite in &suites_to_run {
        println!(
            "\n{} {} {}",
            "═".repeat(20),
            format!("Testing {}", suite).bright_cyan().bold(),
            "═".repeat(20)
        );

        // Step 1: Build the test binary using cargo verus
        println!("🔨 Building test binary for '{}'...", suite);

        let mut cmd = Command::new("cargo");
        cmd.arg("verus").arg("build").arg("--bin").arg(suite);

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

        // Step 2: Find and execute the compiled binary
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
        let test_output = test_cmd
            .output()
            .with_context(|| format!("Failed to execute test binary: {:?}", binary_path))?;

        if test_output.status.success() {
            println!("✓ Test suite '{}' {}", suite, "PASSED".bright_green().bold());

            // Print output for successful tests too
            let stdout = String::from_utf8_lossy(&test_output.stdout);
            if !stdout.is_empty() {
                println!("{}", stdout);
            }
        } else {
            println!("✗ Test suite '{}' {}", suite, "FAILED".bright_red().bold());
            all_passed = false;

            // Print test output for debugging
            let stdout = String::from_utf8_lossy(&test_output.stdout);
            let stderr = String::from_utf8_lossy(&test_output.stderr);

            if !stdout.is_empty() {
                println!("{}", "TEST STDOUT:".bright_yellow());
                println!("{}", stdout);
            }

            if !stderr.is_empty() {
                println!("{}", "TEST STDERR:".bright_yellow());
                println!("{}", stderr);
            }
        }
    }

    // Final summary
    println!("\n{}", "═".repeat(60));
    if all_passed {
        println!("🎉 All tests {} ({})", "PASSED".bright_green().bold(), suites_to_run.len());
    } else {
        println!("💥 Some tests {} ({})", "FAILED".bright_red().bold(), suites_to_run.len());
        bail!("Test execution failed");
    }

    Ok(())
}

fn line_count() -> Result<()> {
    println!("{} Verus Line Count Tool", "📊".bright_cyan().bold());

    // Check if `line_count` has been installed.
    if which::which("line_count").is_err() {
        println!(
            "{} `line_count` not found, installing it from Verus...", "❌".bright_cyan());
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

    // Step 1: Generate dependency information for deko-core and deko-std
    println!("{} Generating dependency information...", "🔍".bright_yellow());

    let project_root = project_root();
    let packages = vec!["deko-core", "deko-std"];
    // let mut dep_files = Vec::new();

    // Discover required binaries first
    let builder = Builder::new("snp".to_string()); // Use SNP as default for line counting
    let verus_binary = builder.find_verus_binary()?;
    let z3_binary = builder.find_z3_binary()?;

    // Set up environment for verus
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

        // Run cargo verus verify with --emit=dep-info
        let mut cmd = Command::new("cargo");
        cmd.arg("verus")
            .arg("verify")
            .arg("--lib")
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

    // Step 2: Parse dep-info files and count lines
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
            .split(" ")
            .filter_map(|f| if f.contains(".rs") || f.contains(".rlib") { Some(f) } else { None })
            .collect::<Vec<_>>();
        // Now combine content into a single string.
        let content = content.join(" ");

        // Write back to the original file.
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

        // print the output.
        let out = cmd.output().with_context(|| {
            format!("Failed to run line_count tool on dep-info file: {:?}", dep_file)
        })?;

        // Store into /target/debug/line_count_output_<package>.txt
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

fn bootstrap_ovmf() -> Result<()> {
    println!("{} Bootstrapping OVMF with COCONUT-SVSM support...", "→".bright_cyan());

    let project_root = project_root();
    let build_dir = project_root.join("/tmp");
    let tools_dir = project_root.join("tools");
    let share_dir = tools_dir.join("share");

    println!("Build directory: {}", build_dir.display().to_string().bright_white());
    println!("Installation destination: {}", share_dir.display().to_string().bright_white());

    // Ensure directories exist
    std::fs::create_dir_all(&build_dir).context("Failed to create build directory")?;
    std::fs::create_dir_all(&share_dir).context("Failed to create tools/share directory")?;

    // Step 1: Clone EDK2 repository
    println!("\n{} Cloning EDK2 repository...", "🔀".bright_yellow());
    let edk2_dir = build_dir.join("edk2");

    if edk2_dir.exists() {
        println!("🗑 Removing existing edk2 directory...");
        std::fs::remove_dir_all(&edk2_dir).context("Failed to remove existing edk2 directory")?;
    }

    let repo_url = "https://github.com/coconut-svsm/edk2.git";
    println!("Cloning from: {}", repo_url.bright_blue());

    let repo = Repository::clone(repo_url, &edk2_dir).context("Failed to clone EDK2 repository")?;
    println!("✓ Cloned EDK2 repository");

    // Step 2: Checkout svsm branch
    println!("\n{} Checking out svsm branch...", "🌿".bright_green());
    std::env::set_current_dir(&edk2_dir).context("Failed to change to EDK2 directory")?;

    let branch_name = "svsm";
    println!("Checking out {} branch...", branch_name);

    // First fetch all remotes to ensure we have the latest branch info
    let mut remote = repo.find_remote("origin").context("Failed to find origin remote")?;
    remote
        .fetch(&["refs/heads/*:refs/remotes/origin/*"], None, None)
        .context("Failed to fetch from origin")?;

    // Now try to find the remote branch
    let remote_branch_name = format!("origin/{}", branch_name);
    let (object, _reference) = repo
        .revparse_ext(&remote_branch_name)
        .with_context(|| format!("Failed to find remote branch {}", remote_branch_name))?;

    // Checkout the remote branch
    repo.checkout_tree(&object, None)?;

    // Check if local branch already exists and handle accordingly
    let branch_ref_name = format!("refs/heads/{}", branch_name);
    if let Ok(_existing_ref) = repo.find_reference(&branch_ref_name) {
        // Local branch exists, just set HEAD to it
        repo.set_head(&branch_ref_name)?;
    } else {
        // Create local branch tracking the remote branch
        repo.reference(&branch_ref_name, object.id(), false, "checkout remote branch")?;
        repo.set_head(&branch_ref_name)?;
    }

    println!("✓ Checked out branch: {}", branch_name);

    // Step 3: Initialize and update git submodules
    println!("\n{} Initializing git submodules...", "📦".bright_yellow());

    let mut cmd = Command::new("git");
    cmd.arg("submodule").arg("init");
    println!("Running: {:?}", cmd);
    let output = cmd.output().context("Failed to initialize git submodules")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Failed to initialize git submodules:\n{}", stderr);
    }
    println!("✓ Git submodules initialized");

    let mut cmd = Command::new("git");
    cmd.arg("submodule").arg("update");
    println!("Running: {:?}", cmd);
    println!("This may take several minutes...");
    let output = cmd.output().context("Failed to update git submodules")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Failed to update git submodules:\n{}", stderr);
    }
    println!("✓ Git submodules updated");

    // Step 4: Set environment variables
    println!("\n{} Setting up environment variables...", "⚙️".bright_cyan());
    std::env::set_var("PYTHON3_ENABLE", "TRUE");
    std::env::set_var("PYTHON_COMMAND", "python3");
    println!("✓ Set PYTHON3_ENABLE=TRUE");
    println!("✓ Set PYTHON_COMMAND=python3");

    // Step 5: Build BaseTools
    println!("\n{} Building BaseTools...", "🔨".bright_green());
    let mut cmd = Command::new("make");
    cmd.arg("-j16").arg("-C").arg("BaseTools/");
    println!("Running: {:?}", cmd);
    println!("This may take several minutes...");

    let output = cmd.output().context("Failed to build BaseTools")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("Failed to build BaseTools:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }
    println!("✓ BaseTools built successfully");

    // Step 6: Run edksetup.sh
    println!("\n{} Running edksetup.sh...", "🔧".bright_blue());
    let mut cmd = Command::new("bash");
    cmd.arg("-c").arg("source ./edksetup.sh --reconfig");
    println!("Running: source ./edksetup.sh --reconfig");

    let output = cmd.output().context("Failed to run edksetup.sh")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("Failed to run edksetup.sh:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }
    println!("✓ edksetup.sh completed");

    // Step 7: Build OVMF firmware
    println!("\n{} Building OVMF firmware...", "🚀".bright_green());
    println!("This will take several minutes...");

    let mut cmd = Command::new("bash");
    cmd.arg("-c").arg(
        "source ./edksetup.sh --reconfig && \
         build -p OvmfPkg/OvmfPkgX64.dsc -a X64 \
         -b DEBUG -t GCC \
         -D DEBUG_ON_SERIAL_PORT \
         -D DEBUG_VERBOSE \
         -D TPM2_ENABLE \
         --pcd PcdUninstallMemAttrProtocol=TRUE",
    );

    println!("Running OVMF build with TPM2 support and debug flags...");

    let output = cmd.output().context("Failed to build OVMF firmware")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("Failed to build OVMF firmware:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }
    println!("✓ OVMF firmware built successfully");

    // Step 8: Copy firmware to tools/share
    println!("\n{} Copying firmware to tools/share...", "📋".bright_cyan());

    let ovmf_source = edk2_dir.join("Build/OvmfX64/DEBUG_GCC/FV/OVMF.fd");
    let ovmf_dest = share_dir.join("OVMF.fd");

    if !ovmf_source.exists() {
        bail!("OVMF.fd not found at expected location: {:?}", ovmf_source);
    }

    std::fs::copy(&ovmf_source, &ovmf_dest).with_context(|| {
        format!("Failed to copy OVMF.fd from {:?} to {:?}", ovmf_source, ovmf_dest)
    })?;

    println!("✓ OVMF firmware copied to: {}", ovmf_dest.display().to_string().bright_white());

    // Step 9: Clean up build directory
    println!("\n{} Cleaning up build directory...", "🧹".bright_cyan());
    if edk2_dir.exists() {
        std::fs::remove_dir_all(&edk2_dir).context("Failed to remove EDK2 build directory")?;
        println!("✓ Removed EDK2 build directory");
    }

    // Print final instructions
    println!(
        "\n{}",
        "=== OVMF firmware bootstrap completed successfully! ===".bright_green().bold()
    );
    println!("OVMF firmware location: {}", ovmf_dest.display().to_string().bright_white());

    println!("\n{}", "Features included:".bright_cyan());
    println!("• TPM2 support enabled (-D TPM2_ENABLE)");
    println!("• Debug output on serial port (-D DEBUG_ON_SERIAL_PORT)");
    println!("• Verbose debugging (-D DEBUG_VERBOSE)");
    println!("• Memory attribute protocol workaround (--pcd PcdUninstallMemAttrProtocol=TRUE)");

    println!(
        "\nThis OVMF binary is ready to use with COCONUT-SVSM and can be packaged into IGVM files."
    );

    Ok(())
}

fn bootstrap_qemu() -> Result<()> {
    println!("{} Bootstrapping QEMU with IGVM support...", "→".bright_cyan());

    // Use tools/ as installation directory
    let project_root = project_root();
    let tools_dir = project_root.join("tools");
    let build_dir = project_root.join("/tmp");

    println!("Installation directory: {}", tools_dir.display().to_string().bright_white());

    // Ensure directories exist
    std::fs::create_dir_all(&build_dir).context("Failed to create build directory")?;
    std::fs::create_dir_all(&tools_dir).context("Failed to create tools directory")?;

    // Step 1: Install cargo-c with nightly toolchain
    println!("\n{} Installing cargo-c...", "📦".bright_yellow());

    std::env::set_var("RUSTUP_TOOLCHAIN", "nightly");
    println!("✓ Set RUSTUP_TOOLCHAIN to nightly for cargo-c installation");

    let mut cmd = Command::new("cargo");
    cmd.arg("install").arg("cargo-c");

    println!("Running: {:?}", cmd);
    let output = cmd.output().context("Failed to install cargo-c")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);

        // Check if already installed
        if stderr.contains("already exists") || stdout.contains("already installed") {
            println!("✓ cargo-c already installed");
        } else {
            bail!("Failed to install cargo-c:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
        }
    } else {
        println!("✓ cargo-c installed successfully");
    }

    // Step 2: Clone and build IGVM library
    println!("\n{} Building IGVM library...", "🔧".bright_green());
    let igvm_dir = build_dir.join("igvm");
    let igvm_install_dir = tools_dir.clone();

    if !igvm_dir.exists() {
        println!("Cloning IGVM repository...");
        let _ = Repository::clone("https://github.com/microsoft/igvm", &igvm_dir)
            .context("Failed to clone IGVM repository")?;
        println!("✓ Cloned IGVM repository");
    } else {
        println!("IGVM repository already exists at {:?}", igvm_dir);
    }

    // Build IGVM library - use cargo cinstall directly in igvm_c directory
    std::env::set_current_dir(&igvm_dir).context("Failed to change to IGVM directory")?;

    // Check directory structure to understand what's available
    println!("Checking IGVM repository structure...");
    println!("Installing IGVM library to: {}", igvm_install_dir.display());

    // Ensure destination directory exists
    std::fs::create_dir_all(&igvm_install_dir).context("Failed to create tools/lib directory")?;

    // Try building the C library directly using cargo cinstall
    let igvm_c_dir = igvm_dir.join("igvm_c");
    if igvm_c_dir.exists() {
        std::env::set_current_dir(&igvm_c_dir).context("Failed to change to igvm_c directory")?;

        let mut cmd = Command::new("cargo");
        cmd.arg("cinstall").arg("--prefix").arg(&igvm_install_dir);

        println!("Running: {:?}", cmd);
        let output = cmd.output().context("Failed to build IGVM library with cargo cinstall")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            bail!("Failed to build IGVM library:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
        }
        println!("✓ IGVM library built and installed to tools/lib");

        // Also manually install header files
        let include_src_dir = igvm_dir.join("igvm_c").join("include");
        let include_dest_dir = igvm_install_dir.join("include/igvm");

        if include_src_dir.exists() {
            std::fs::create_dir_all(&include_dest_dir)
                .context("Failed to create include directory")?;

            for entry in std::fs::read_dir(&include_src_dir)? {
                let entry = entry?;
                let src_path = entry.path();
                if src_path.is_file() {
                    let dest_path = include_dest_dir.join(entry.file_name());
                    std::fs::copy(&src_path, &dest_path)
                        .with_context(|| format!("Failed to copy header file: {:?}", src_path))?;
                }
            }
            println!("✓ IGVM header files installed to tools/include/igvm");
        } else {
            println!("⚠ IGVM include directory not found, skipping header installation");
        }
    } else {
        bail!("IGVM repository structure is not as expected - igvm_c directory not found");
    }

    // Step 3: Clone and build QEMU with IGVM support
    println!("\n{} Building QEMU with IGVM support...", "⚙️".bright_green());
    let qemu_dir = build_dir.join("qemu");

    if !qemu_dir.exists() {
        println!("Cloning QEMU repository...");
        let _ = Repository::clone("https://github.com/coconut-svsm/qemu", &qemu_dir)
            .context("Failed to clone QEMU repository")?;
        println!("✓ Cloned QEMU repository");
    } else {
        println!("QEMU repository already exists at {:?}", qemu_dir);
    }

    // Checkout the svsm-igvm branch
    let repo = Repository::open(&qemu_dir).context("Failed to open QEMU repository")?;
    let branch_name = "svsm-igvm";

    println!("Checking out {} branch...", branch_name);

    // First fetch all remotes to ensure we have the latest branch info
    let mut remote = repo.find_remote("origin").context("Failed to find origin remote")?;
    remote
        .fetch(&["refs/heads/*:refs/remotes/origin/*"], None, None)
        .context("Failed to fetch from origin")?;

    // Now try to find the remote branch
    let remote_branch_name = format!("origin/{}", branch_name);
    let (object, _reference) = repo
        .revparse_ext(&remote_branch_name)
        .with_context(|| format!("Failed to find remote branch {}", remote_branch_name))?;

    // Checkout the remote branch
    repo.checkout_tree(&object, None)?;

    // Check if local branch already exists and handle accordingly
    let branch_ref_name = format!("refs/heads/{}", branch_name);
    if let Ok(_existing_ref) = repo.find_reference(&branch_ref_name) {
        // Local branch exists, just set HEAD to it
        repo.set_head(&branch_ref_name)?;
    } else {
        // Create local branch tracking the remote branch
        repo.reference(&branch_ref_name, object.id(), false, "checkout remote branch")?;
        repo.set_head(&branch_ref_name)?;
    }

    println!("✓ Checked out branch: {}", branch_name);

    // Configure QEMU
    std::env::set_current_dir(&qemu_dir).context("Failed to change to QEMU directory")?;

    let qemu_install_dir = tools_dir.clone();
    // No need to create qemu_install_dir as tools_dir already exists

    println!("Configuring QEMU...");
    println!("  QEMU install directory: {}", qemu_install_dir.display());

    // Set up environment variables for IGVM library discovery
    let pkgconfig_path = format!(
        "{}:{}",
        igvm_install_dir.join("lib/x86_64-linux-gnu/pkgconfig").display(),
        std::env::var("PKG_CONFIG_PATH").unwrap_or_default()
    );

    let c_include_path = format!(
        "{}:{}",
        igvm_install_dir.join("include/igvm").display(),
        std::env::var("C_INCLUDE_PATH").unwrap_or_default()
    );

    let library_path = format!(
        "{}:{}",
        igvm_install_dir.join("lib").display(),
        std::env::var("LIBRARY_PATH").unwrap_or_default()
    );

    let mut cmd = Command::new("./configure");
    cmd.env("PKG_CONFIG_PATH", &pkgconfig_path);
    cmd.env("C_INCLUDE_PATH", &c_include_path);
    cmd.env("LIBRARY_PATH", &library_path);
    cmd.arg(format!("--prefix={}", qemu_install_dir.display()))
        .arg("--target-list=x86_64-softmmu")
        .arg("--enable-igvm");

    println!("Running: {:?}", cmd);
    println!("  PKG_CONFIG_PATH: {}", pkgconfig_path);
    println!("  C_INCLUDE_PATH: {}", c_include_path);
    println!("  LIBRARY_PATH: {}", library_path);

    let output = cmd.output().context("Failed to configure QEMU")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("Failed to configure QEMU:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }
    println!("✓ QEMU configured successfully");

    // Build QEMU with ninja
    println!("Building QEMU with ninja...");
    println!("This may take several minutes...");

    let c_include_path = format!(
        "{}:{}",
        igvm_install_dir.join("include").display(),
        std::env::var("C_INCLUDE_PATH").unwrap_or_default()
    );

    let library_path = format!(
        "{}:{}",
        igvm_install_dir.join("lib/x86_64-linux-gnu").display(),
        std::env::var("LIBRARY_PATH").unwrap_or_default()
    );

    let mut cmd = Command::new("ninja");
    cmd.arg("-C").arg("build/");
    cmd.env("C_INCLUDE_PATH", &c_include_path);
    cmd.env("LIBRARY_PATH", &library_path);

    println!("Running: {:?}", cmd);
    let output = cmd.output().context("Failed to build QEMU with ninja")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Failed to build QEMU:\n{}", stderr);
    }
    println!("✓ QEMU built successfully");

    // Install QEMU
    println!("Installing QEMU to tools/bin...");
    let mut cmd = Command::new("make");
    cmd.arg("install");

    let output = cmd.output().context("Failed to install QEMU")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Failed to install QEMU:\n{}", stderr);
    }

    println!("✓ QEMU installed successfully");

    // Clean up temporary build directories
    println!("\n{} Cleaning up build directories...", "🧹".bright_cyan());

    if igvm_dir.exists() {
        std::fs::remove_dir_all(&igvm_dir).context("Failed to remove IGVM build directory")?;
        println!("✓ Removed IGVM build directory");
    }

    if qemu_dir.exists() {
        std::fs::remove_dir_all(&qemu_dir).context("Failed to remove QEMU build directory")?;
        println!("✓ Removed QEMU build directory");
    }

    // Print final instructions
    println!(
        "\n{}",
        "=== QEMU with IGVM support installed successfully! ===".bright_green().bold()
    );
    println!(
        "QEMU binary location: {}",
        qemu_install_dir.join("bin/qemu-system-x86_64").display().to_string().bright_white()
    );
    println!("IGVM library location: {}", igvm_install_dir.display().to_string().bright_white());

    println!("\nTo use this QEMU, you can:");
    println!("• Add tools/bin/qemu-svsm/bin to your PATH:");
    println!(
        "  export PATH={}:$PATH",
        qemu_install_dir.join("bin").display().to_string().bright_blue()
    );
    println!("• Or use the full path when running QEMU:");
    println!(
        "  {}",
        qemu_install_dir.join("bin/qemu-system-x86_64").display().to_string().bright_blue()
    );

    Ok(())
}

fn bootstrap_verus(prefix: &Path, commit: Option<&str>, branch: Option<&str>) -> Result<()> {
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

    let repo_url = "https://github.com/hiroki-chen/verus.git";
    println!("Cloning from: {}", repo_url.bright_blue());

    let repo =
        Repository::clone(repo_url, &verus_dir).context("Failed to clone Verus repository")?;

    // Checkout specific commit or branch if provided
    match (commit, branch) {
        (Some(commit_hash), None) => {
            println!("Checking out commit: {}", commit_hash.bright_yellow());
            let (object, _) = repo
                .revparse_ext(commit_hash)
                .with_context(|| format!("Failed to find commit {}", commit_hash))?;
            repo.checkout_tree(&object, None).context("Failed to checkout commit")?;
            repo.set_head_detached(object.id()).context("Failed to set HEAD to commit")?;
        }
        (None, Some(branch_name)) => {
            println!("Checking out branch: {}", branch_name.bright_green());

            // First fetch all remotes to ensure we have the latest branch info
            let mut remote = repo.find_remote("origin").context("Failed to find origin remote")?;
            remote
                .fetch(&["refs/heads/*:refs/remotes/origin/*"], None, None)
                .context("Failed to fetch from origin")?;

            // Try to find the remote branch
            let remote_branch_name = format!("origin/{}", branch_name);
            let (object, _) = repo
                .revparse_ext(&remote_branch_name)
                .with_context(|| format!("Failed to find remote branch {}", remote_branch_name))?;

            // Checkout the remote branch
            repo.checkout_tree(&object, None)?;

            // Check if local branch already exists and handle accordingly
            let branch_ref_name = format!("refs/heads/{}", branch_name);
            if let Ok(_existing_ref) = repo.find_reference(&branch_ref_name) {
                // Local branch exists, just set HEAD to it
                repo.set_head(&branch_ref_name)?;
            } else {
                // Create local branch tracking the remote branch
                repo.reference(&branch_ref_name, object.id(), false, "checkout remote branch")?;
                repo.set_head(&branch_ref_name)?;
            }

            println!("✓ Checked out branch: {}", branch_name);
        }
        (Some(_), Some(_)) => {
            bail!("Cannot specify both commit and branch - please choose one");
        }
        (None, None) => {
            println!("✓ Using default branch");
        }
    }

    println!("✓ Repository cloned successfully!");

    // Copy our project's rust-toolchain.toml to verus directory to ensure same nightly version
    println!("\n{} Synchronizing Rust toolchain with project...", "🔄".bright_yellow());
    let project_toolchain_path = project_root().join("rust-toolchain.toml");
    let verus_toolchain_path = verus_dir.join("rust-toolchain.toml");

    if project_toolchain_path.exists() {
        let toolchain_content = std::fs::read_to_string(&project_toolchain_path)
            .context("Failed to read project's rust-toolchain.toml")?;
        std::fs::write(&verus_toolchain_path, &toolchain_content)
            .context("Failed to write Verus rust-toolchain.toml")?;
        println!("✓ Copied project's rust-toolchain.toml to Verus directory");

        // Extract the channel version for display
        let rust_version = toolchain_content
            .lines()
            .find(|line| line.trim_start().starts_with("channel"))
            .and_then(|line| line.split('=').nth(1))
            .map(|s| s.trim().trim_matches('"'))
            .unwrap_or("unknown");
        println!("✓ Using Rust toolchain: {}", rust_version.bright_white());
    } else {
        println!("⚠ No project rust-toolchain.toml found, using Verus default");
    }

    // Enter the verus directory
    std::env::set_current_dir(&verus_dir).context("Failed to change to verus directory")?;
    println!("✓ Changed to verus directory: {}", verus_dir.display().to_string().bright_white());

    // Extract rust version from the toolchain content for rustup override
    let rust_version = if project_toolchain_path.exists() {
        let toolchain_content = std::fs::read_to_string(&project_toolchain_path)
            .context("Failed to read project's rust-toolchain.toml")?;
        toolchain_content
            .lines()
            .find(|line| line.trim_start().starts_with("channel"))
            .and_then(|line| line.split('=').nth(1))
            .map(|s| s.trim().trim_matches('"').to_string())
            .unwrap_or_else(|| "nightly".to_string())
    } else {
        "nightly".to_string()
    };

    // Step 2: Change to source directory
    let source_dir = verus_dir.join("source");
    if !source_dir.exists() {
        bail!("Source directory not found at: {:?}", source_dir);
    }

    println!("\n{} Changing to source directory: {}", "📂".bright_cyan(), source_dir.display());
    std::env::set_current_dir(&source_dir).context("Failed to change to source directory")?;

    let mut cmd = Command::new("rustup");
    cmd.arg("override").arg("set").arg(&rust_version);
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
        std::fs::remove_dir_all(&verus_dir)
            .context("Failed to delete temporary verus build directory")?;
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
    // Try to get the manifest directory from environment variable first
    if let Ok(manifest_dir) = std::env::var("CARGO_MANIFEST_DIR") {
        Path::new(&manifest_dir).ancestors().nth(1).unwrap().to_path_buf()
    } else {
        // Fallback: assume we're in the xtask subdirectory and go up one level
        std::env::current_dir().unwrap().parent().unwrap_or_else(|| Path::new(".")).to_path_buf()
    }
}
