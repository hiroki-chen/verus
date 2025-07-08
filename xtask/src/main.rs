use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand, ValueEnum};
use serde::Deserialize;

const DEFAULT_STAGE1_PATH: &str =
    "/home/haobchen/cage-sev/target/x86_64-unknown-uefi/release/deko-stage1.efi";
const DEFAULT_OVMF_PATH: &str = "~/.local/share/ovmf/OVMF.fd";
/// This is for SEV stage 2 boot.
const DEFAULT_DEKO_MONITOR_PATH: &str =
    "/home/haobchen/cage-sev/target/x86_64-sev-deko/release/deko-monitor.bin";

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
}

#[derive(ValueEnum, Debug, Clone)]
enum BuildTarget {
    Deko,
    Stage1,
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
    #[arg(short, long, value_enum)]
    target_arch: TargetArch,
}

#[derive(Subcommand, Debug)]
enum Commands {
    CreateBootable {
        #[arg(short, long)]
        ovmf_path: Option<String>,
        #[arg(short, long)]
        deko_monitor_path: Option<String>,
        #[arg(short, long)]
        stage1_path: Option<String>,
    },

    Qemu {
        #[arg(short, long)]
        config_path: Option<String>,
    },

    Build {
        #[arg(short, long, value_enum)]
        target: BuildTarget,
        #[arg(short, long)]
        release: bool,
    },
}

impl Default for FinalQemuConfig {
    fn default() -> Self {
        FinalQemuConfig {
            memory: "4G".to_string(),
            smp_cores: 4,
            enable_cvm: true,
            enable_graphics: false, // Default to nographic
            drive: vec![],
            igvm_path: project_root().join("target/release/igvm.igvm").display().to_string(),
            debug: false,
            bios_path: "/usr/local/share/ovmf/OVMF.fd".to_string(),
        }
    }
}

struct Builder {
    target_arch: String,
}

impl Builder {
    pub fn new(target_arch: String) -> Self { Builder { target_arch } }

    pub fn build(&self, target: BuildTarget, release: bool) -> Result<()> {
        match target {
            BuildTarget::Deko => {
                // Change the working directory to the deko-monitor package
                let deko_monitor = project_root().join("deko-monitor");
                std::env::set_current_dir(&deko_monitor)
                    .context("Failed to change directory to deko-monitor")?;
                let mut cmd = std::process::Command::new("cargo");
                cmd.arg("verus")
                    .arg("build")
                    .arg("--target")
                    .arg(format!("../.cargo/{}.json", self.target_arch));

                if release {
                    cmd.arg("--release");
                } else {
                    cmd.arg("--debug");
                }

                println!("Building Deko with command: {:?}", cmd);
                if !cmd.status()?.success() {
                    bail!("Cannot build deko");
                }

                if self.target_arch.contains("sev") {
                    // Creating flat image
                    cmd = std::process::Command::new("objcopy");
                    cmd.arg("-O")
                        .arg("binary")
                        .arg("../target/x86_64-sev-deko/release/deko-monitor")
                        .arg("../target/x86_64-sev-deko/release/deko-monitor.bin");

                    println!("Creating flat image with command: {:?}", cmd);
                    if !cmd.status()?.success() {
                        bail!("Cannot create flat image for deko-monitor");
                    }
                }

                Ok(())
            }
            BuildTarget::Stage1 => {
                let mut cmd = std::process::Command::new("cargo");
                cmd.arg("build")
                    .arg("--package")
                    .arg("deko-stage1")
                    .arg("--target")
                    .arg("x86_64-unknown-uefi");

                if release {
                    cmd.arg("--release");
                }

                println!("Building Stage1 with command: {:?}", cmd);
                if !cmd.status()?.success() {
                    bail!("Failed to build stage1");
                }

                Ok(())
            }
        }
    }

    pub fn qemu(&self, config_path: &str) -> Result<()> {
        let config = match load_qemu_config(config_path) {
            Ok(cfg) => cfg,
            Err(_) => Default::default(),
        };

        println!("--- Launching QEMU ---");
        println!("Configuration: {:#?}", config);

        let mut cmd = std::process::Command::new("qemu-system-x86_64");
        cmd.args(["-accel", "kvm", "-cpu", "host"]);
        cmd.arg("-smp").arg(config.smp_cores.to_string());

        // Add drives
        for (i, drive) in config.drive.iter().enumerate() {
            cmd.arg("-drive").arg(format!(
                "file={},if={},format={},id=disk{}",
                drive.file.to_str().unwrap(),
                drive.interface,
                drive.format,
                i
            ));
        }

        // Graphics configuration
        if config.enable_graphics {
            // Keeps default graphics
        } else {
            cmd.args(["-nographic", "-vga", "none"]);
        }

        // Low-level machine and serial config
        cmd.args(["-serial", "stdio", "-nodefaults", "-no-reboot"]);

        if config.enable_cvm {
            if self.target_arch.contains("sev") {
                qemu_sev(&config, &mut cmd);
            } else if self.target_arch.contains("tdx") {
                qemu_tdx(&config, &mut cmd);
            } else {
                bail!("Unsupported target architecture: {}", self.target_arch);
            }
        }

        if config.debug {
            // Additional debugging options
            cmd.args(["-s", "-S"]); // -s for gdb server, -S for pause on startup
            println!("Debugging mode enabled: QEMU will start with GDB server and paused state.");
        }

        println!("Executing command: {:?}", cmd);

        let mut child = cmd.spawn().context("Failed to spawn QEMU")?;
        child.wait().context("QEMU process failed")?;

        println!("Running QEMU with the following configuration:");

        Ok(())
    }

    pub fn create_bootable(
        &self,
        ovmf_path: &str,
        deko_monitor_path: &str,
        stage1_path: &str,
    ) -> Result<()> {
        match &self.target_arch {
            target if target.contains("sev") => self
                .create_bootable_sev(ovmf_path, deko_monitor_path)
                .context("Failed to create bootable SEV image"),
            target if target.contains("tdx") => {
                // Placeholder for TDX logic
                self.create_bootable_tdx(deko_monitor_path, stage1_path)
                    .context("Failed to create bootable TDX image")
            }
            _ => bail!("Unsupported target architecture: {}", self.target_arch),
        }
    }

    fn create_bootable_tdx(&self, deko_monitor_path: &str, stage1_path: &str) -> Result<()> {
        self.build(BuildTarget::Stage1, true)?;

        // Logic to create a bootable image using the provided paths
        let loader_path = project_root().join(stage1_path);
        let deko_monitor_path = project_root().join(deko_monitor_path);
        let boot_img_path = project_root().join("target/x86_64-tdx-deko/release/boot.img");

        println!("Creating bootable image with:");
        println!("Loader Path: {:?}", loader_path);
        println!("Deko Monitor Path: {:?}", deko_monitor_path);
        println!("Boot Image Path: {:?}", boot_img_path);

        let img_file = OpenOptions::new()
            .read(true) // We need to read from it after formatting.
            .write(true) // We need to write to it to format and copy files.
            .create(true) // Create it if it doesn't exist.
            .truncate(true) // Truncate it to zero if it already exists.
            .open(&boot_img_path)
            .context("Failed to create or open boot image file")?;
        // Zeros out the file to ensure it's empty
        let img_len = 1024 * 1024 * 64; // 64 MB
        img_file.set_len(img_len as u64).context("Failed to set boot image file size")?;

        let format_options = fatfs::FormatVolumeOptions::new();
        fatfs::format_volume(&img_file, format_options).context("Failed to format boot image")?;

        let fs = fatfs::FileSystem::new(&img_file, fatfs::FsOptions::new())
            .context("Failed to initialize filesystem")?;
        let root_dir = fs.root_dir();
        let efi_dir = root_dir.create_dir("EFI").context("Failed to create EFI directory")?;
        let boot_dir = efi_dir.create_dir("BOOT").context("Failed to create BOOT directory")?;

        let mut dest_file =
            boot_dir.create_file("BOOTX64.EFI").context("Failed to create BOOTX64.EFI file")?;
        dest_file.truncate()?;
        std::io::copy(&mut fs::File::open(loader_path)?, &mut dest_file)?;

        let mut dest_file = root_dir.create_file("deko.bin")?;
        dest_file.truncate()?;
        std::io::copy(&mut fs::File::open(deko_monitor_path)?, &mut dest_file)?;

        println!("--- Boot Image created at {:?} ---", boot_img_path);
        Ok(())
    }

    fn create_bootable_sev(&self, ovmf_path: &str, deko_monitor_path: &str) -> Result<()> {
        // First ensure that our package is fresh.
        self.build(BuildTarget::Deko, true)?;

        // Logic to create a bootable image using the provided paths
        let deko_monitor_path = project_root().join(deko_monitor_path);
        let boot_img_path = project_root().join("target/release/igvm.igvm");
        // Get full path to OVMF
        let ovmf_path = shellexpand::tilde(ovmf_path);

        println!("Creating IGVM image with:");
        println!("Deko Monitor Path: {:?}", deko_monitor_path);
        println!("IGVM Image Path: {:?}", boot_img_path);

        let mut cmd = std::process::Command::new("igvmbuilder");
        cmd.args(["--sort", "--policy", "0x30000", "--snp"]);
        cmd.args(["--firmware", ovmf_path.to_string().as_str()]);
        // Stage 2 has some problems.
        cmd.args(["--stage2", deko_monitor_path.to_str().unwrap()]);
        cmd.args([
            "--kernel",
            "/home/haobchen/cage-sev/target/x86_64-sev-deko/release/deko-monitor",
        ]);
        cmd.args(["--output", boot_img_path.to_str().unwrap()]);
        cmd.arg("qemu");

        println!("Executing command: {:?}", cmd);

        let mut child = cmd.spawn().context("Failed to spawn igvmbuilder")?;
        child.wait().context("igvmbuilder process failed")?;

        println!("--- IGVM Image created at {:?} ---", boot_img_path);
        Ok(())
    }
}

fn qemu_sev(config: &FinalQemuConfig, cmd: &mut std::process::Command) {
    // SEV specific configuration
    cmd.arg("-machine").arg(format!(
        "type=q35,confidential-guest-support=sev,kernel_irqchip=split,igvm-cfg=igvm,memory-backend=ram"
    ));
    cmd.args(["-object", "sev-snp-guest,id=sev,reduced-phys-bits=1,cbitpos=51"]);
    cmd.arg("-object").arg(format!("memory-backend-memfd,id=ram,size={}", config.memory));
    cmd.arg("-object").arg(format!("igvm-cfg,id=igvm,file={}", config.igvm_path));
}

fn qemu_tdx(config: &FinalQemuConfig, cmd: &mut std::process::Command) {
    cmd.arg("-machine").arg(format!(
        "type=q35,confidential-guest-support=tdx,kernel_irqchip=split,memory-backend=ram0"
    ));

    let tdx_arg = if config.debug { "tdx-guest,id=tdx,debug=on" } else { "tdx-guest,id=tdx" };

    cmd.args(["-object", tdx_arg]);
    cmd.args(["-object", "iommufd,id=iommufd0"]);
    cmd.arg("-object").arg(format!("memory-backend-ram,id=ram0,size={}", config.memory));
    cmd.args(["-bios", config.bios_path.as_str()]);
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let target_arch = match cli.target_arch {
        TargetArch::Tdx => "x86_64-tdx-deko",
        TargetArch::Snp => "x86_64-sev-deko",
    };

    let builder = Builder::new(target_arch.to_string());
    match cli.command {
        Commands::CreateBootable { ovmf_path, deko_monitor_path, stage1_path } => {
            if let Some(loader) = &ovmf_path {
                println!("Using OVMF path: {}", loader);
            } else {
                println!("No loader path provided, using default.");
            }

            if let Some(deko_monitor) = &deko_monitor_path {
                println!("Using deko monitor path: {}", deko_monitor);
            } else {
                println!("No deko monitor path provided, using default.");
            }

            builder.create_bootable(
                ovmf_path.as_deref().unwrap_or(DEFAULT_OVMF_PATH),
                deko_monitor_path.as_deref().unwrap_or(DEFAULT_DEKO_MONITOR_PATH),
                stage1_path.as_deref().unwrap_or(DEFAULT_STAGE1_PATH),
            )
        }
        Commands::Qemu { config_path } => {
            if let Some(path) = &config_path {
                println!("Using QEMU config path: {}", path);
            } else {
                println!("No QEMU config path provided, using default.");
            }
            // Here you would implement the logic to run QEMU with the provided config
            // For now, we just print a message
            println!("Running QEMU with the specified configuration...");

            let config_path = config_path.unwrap_or_else(|| {
                project_root().join(".config/qemu.config.toml").display().to_string()
            });

            builder.qemu(&config_path).context("Failed to run QEMU")
        }
        Commands::Build { target, release } => builder.build(target, release),
    }
}

fn load_qemu_config(path: &str) -> Result<FinalQemuConfig> {
    // Logic to load QEMU configuration from the specified path
    let config_path = PathBuf::from(path);
    let mut config = FinalQemuConfig::default();

    if config_path.try_exists()? {
        println!("Loading QEMU configuration from: {:?}", config_path);
        // Here you would parse the config file and populate the `config` variable
        // For now, we just print a message
    } else {
        println!("Config file not found at: {:?}", config_path);
        return Err(anyhow::anyhow!("QEMU configuration file not found"));
    }

    let partial = toml::from_str::<PartialQemuConfig>(
        &fs::read_to_string(&config_path).context("Failed to read QEMU config file")?,
    )
    .context("Failed to parse QEMU config file")?;

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
    // For drive, the user's config completely replaces the default.
    if let Some(drive) = partial.drive {
        config.drive = drive;
    }

    if let Some(debug) = partial.debug {
        config.debug = debug;
    }

    Ok(config)
}

fn project_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).ancestors().nth(1).unwrap().to_path_buf()
}
