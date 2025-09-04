use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use clap::{Parser, Subcommand, ValueEnum};
use git2::Repository;
use serde::Deserialize;

// Configuration constants - no user-specific paths
const DEFAULT_VERUS_REPO: &str = "https://github.com/hiroki-chen/verus.git";
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

    fn boot_image_path(&self) -> PathBuf { self.target_dir(true).join("boot.img") }

    fn igvm_path(&self) -> PathBuf { self.target_dir(true).join("igvm.igvm") }

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
        prefix: PathBuf,
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

    fn build_deko(&self, release: bool) -> Result<()> {
        println!("--- Building stage2 bootloader ---");

        let deko_stage2 = self.config.root.join("deko-core");
        std::env::set_current_dir(&deko_stage2)
            .context("Failed to change directory to deko-core")?;

        // Build stage2
        let mut cmd = std::process::Command::new("cargo");
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

        println!("Building with command: {:?}", cmd);
        if !cmd.status()?.success() {
            bail!("Cannot build deko-stage2");
        }

        // Create flat image for SNP
        if self.config.target_arch == "snp" {
            let mut cmd = std::process::Command::new("objcopy");
            cmd.arg("-O")
                .arg("binary")
                .arg(self.config.stage2_path(release))
                .arg(self.config.stage2_binary_path(release));

            println!("Creating flat image with command: {:?}", cmd);
            if !cmd.status()?.success() {
                bail!("Cannot create flat image for deko-monitor");
            }
        }

        println!("--- Building Deko Monitor ---");

        // Build monitor
        let mut cmd = std::process::Command::new("cargo");
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

        if !cmd.status()?.success() {
            bail!("Cannot build deko-monitor");
        }

        // Create ELF for SNP
        if self.config.target_arch == "snp" {
            let mut cmd = std::process::Command::new("objcopy");
            cmd.arg("-O")
                .arg("elf64-x86-64")
                .arg("--strip-unneeded")
                .arg(self.config.deko_monitor_path(release))
                .arg(self.config.deko_elf_path(release));

            println!("Creating ELF image with command: {:?}", cmd);
            if !cmd.status()?.success() {
                bail!("Cannot create ELF image for deko-monitor");
            }
        }

        Ok(())
    }

    fn build_stage1(&self, release: bool) -> Result<()> {
        let mut cmd = std::process::Command::new("cargo");
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

        println!("Building Stage1 with command: {:?}", cmd);
        if !cmd.status()?.success() {
            bail!("Failed to build stage1");
        }

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
        self.build(BuildTarget::Deko, true)?;

        let stage2_path = stage2_path.unwrap_or_else(|| self.config.stage2_binary_path(true));
        let boot_img_path = self.config.igvm_path();
        let ovmf_path = ovmf_path.unwrap_or_else(ProjectConfig::default_ovmf_path);
        let kernel_path = self.config.deko_monitor_path(true);

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

        Commands::BootstrapVerus { prefix, commit } => bootstrap_verus(&prefix, commit.as_deref()),

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
    println!("Bootstrapping with prefix: {}", prefix.display());

    // Ensure prefix directory exists
    std::fs::create_dir_all(prefix).context("Failed to create prefix directory")?;

    let verus_dir = prefix.join("verus");

    // Clone or update repository
    if verus_dir.exists() {
        println!("Verus repository already exists at {}, using existing repo", verus_dir.display());

        let repo = Repository::open(&verus_dir).context("Failed to open existing repository")?;

        if let Some(commit) = commit {
            repo.set_head_detached(repo.revparse_single(commit)?.id())?;
            println!("Checked out commit: {}", commit);
        }
    } else {
        println!("Cloning Verus repository to {}", verus_dir.display());
        let repo = Repository::clone(DEFAULT_VERUS_REPO, &verus_dir)?;

        if let Some(commit) = commit {
            repo.set_head_detached(repo.revparse_single(commit)?.id())?;
            println!("Checked out commit: {}", commit);
        }
    }

    // Step 3: Build Verus (following the official instructions)
    let source_dir = verus_dir.join("source");
    let activate_script = verus_dir.join("tools/activate");

    // Check if activation script exists
    if !activate_script.exists() {
        bail!("Activation script not found at {:?}", activate_script);
    }

    println!("Building Verus with development environment...");

    // Change to source directory
    std::env::set_current_dir(&source_dir)
        .with_context(|| format!("Failed to change directory to {:?}", source_dir))?;

    // Detect the shell
    let shell = detect_shell();
    println!("Detected shell: {}", shell);

    // Build command that sources activate script and runs vargo build
    let build_command = match shell.as_str() {
        "fish" => {
            format!("source ../tools/activate.fish && vargo build --release",)
        }
        _ => {
            // bash/zsh/sh
            format!("source ../tools/activate && vargo build --release",)
        }
    };

    // Install z3.
    println!("Installing z3...");
    let mut z3_cmd = std::process::Command::new("bash");
    z3_cmd.arg("-c").arg("./tools/get-z3.sh");
    if !z3_cmd.status()?.success() {
        bail!("Failed to install z3");
    }
    println!("✓ z3 installed successfully");

    println!("Running build in development environment...");
    println!("Command: {}", build_command);

    let mut cmd = std::process::Command::new(&shell);
    cmd.arg("-c").arg(&build_command).current_dir(&source_dir).env("RUST_BACKTRACE", "1");

    // Run the build
    let output = cmd.output().context("Failed to execute vargo build")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        bail!("Failed to build verus:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }

    // Check for success indicators in output
    let stdout = String::from_utf8_lossy(&output.stdout);
    if stdout.contains("Verified") || stdout.contains("vstd") {
        println!("✓ Verus built and vstd verified successfully");
    } else {
        println!("✓ Verus build completed");
    }

    println!("✓ Bootstrap completed successfully!");

    // Print final instructions
    println!("\nVerus installation complete!");
    println!("Verus binary should be at: {:?}", source_dir.join("target-verus/release/verus"));
    println!("\nTo use Verus, source the activation script:");
    match shell.as_str() {
        "fish" => println!("  source {:?}", verus_dir.join("tools/activate.fish")),
        _ => println!("  source {:?}", verus_dir.join("tools/activate")),
    }
    println!("Then run: vargo build --release");

    Ok(())
}

// Helper function to detect the current shell
fn detect_shell() -> String {
    // Try to get shell from environment
    if let Ok(shell) = std::env::var("SHELL") {
        if shell.contains("fish") {
            return "fish".to_string();
        } else if shell.contains("zsh") {
            return "zsh".to_string();
        } else if shell.contains("bash") {
            return "bash".to_string();
        }
    }

    // Default to bash
    "bash".to_string()
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

    for file in &rs_files {
        println!("Formatting: {:?}", file);
        let mut cmd = std::process::Command::new("verusfmt");
        cmd.arg(&file).arg(&file);
        if !cmd.status()?.success() {
            eprintln!("Warning: Failed to format file: {:?}", file);
        }
    }

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

fn project_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).ancestors().nth(1).unwrap().to_path_buf()
}
