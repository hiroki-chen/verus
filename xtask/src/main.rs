use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::{Parser, Subcommand, ValueEnum};
use serde::Deserialize;

const DEFAULT_LOADER_PATH: &str = "target/x86_64-unknown-uefi/release/deko-stage1.efi";
const DEFAULT_DEKO_MONITOR_PATH: &str = "target/x86_64-tdx-deko/release/deko-monitor";

#[derive(Debug)]
struct FinalQemuConfig {
    memory: String,
    smp_cores: u32,
    bios_path: PathBuf,
    enable_tdx: bool,
    enable_graphics: bool, // Unified graphic/nographic switch
    drive: Vec<DriveConfig>,
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
    bios_path: Option<PathBuf>,
    enable_tdx: Option<bool>,
    enable_graphics: Option<bool>,
    drive: Option<Vec<DriveConfig>>,
}

#[derive(ValueEnum, Debug, Clone)]
enum BuildTarget {
    Stage1,
    Deko,
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    CreateBootable {
        #[arg(short, long)]
        loader_path: Option<String>,
        #[arg(short, long)]
        deko_monitor_path: Option<String>,
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
            bios_path: PathBuf::from("/cc/tdx-linux/edk2/OVMF.fd"),
            enable_tdx: true,
            enable_graphics: false, // Default to nographic
            drive: vec![DriveConfig {
                file: project_root().join("target/release/boot.img"),
                format: "raw".to_string(),
                interface: "virtio".to_string(),
            }],
        }
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::CreateBootable { loader_path, deko_monitor_path } => {
            if let Some(loader) = &loader_path {
                println!("Using loader path: {}", loader);
            } else {
                println!("No loader path provided, using default.");
            }

            if let Some(deko_monitor) = &deko_monitor_path {
                println!("Using deko monitor path: {}", deko_monitor);
            } else {
                println!("No deko monitor path provided, using default.");
            }

            create_bootable(
                loader_path.as_deref().unwrap_or(DEFAULT_LOADER_PATH),
                deko_monitor_path.as_deref().unwrap_or(DEFAULT_DEKO_MONITOR_PATH),
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
                project_root().join(".config/qemu_config.toml").display().to_string()
            });

            qemu(&config_path).context("Failed to run QEMU")
        }
        Commands::Build { target, release } => build(target, release),
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
    if let Some(bios) = partial.bios_path {
        config.bios_path = bios;
    }
    if let Some(tdx) = partial.enable_tdx {
        config.enable_tdx = tdx;
    }
    if let Some(graphics) = partial.enable_graphics {
        config.enable_graphics = graphics;
    }

    // For drive, the user's config completely replaces the default.
    if let Some(drive) = partial.drive {
        config.drive = drive;
    }

    Ok(config)
}

fn project_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).ancestors().nth(1).unwrap().to_path_buf()
}

fn build(target: BuildTarget, release: bool) -> Result<()> {
    match target {
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
            cmd.status().context("Failed to build Stage1")?;
        }
        BuildTarget::Deko => {
            // Change the working directory to the deko-monitor package
            let deko_core_path = project_root().join("deko-monitor");
            std::env::set_current_dir(&deko_core_path)
                .context("Failed to change directory to deko-monitor")?;
            let mut cmd = std::process::Command::new("cargo");
            cmd.arg("verus").arg("build").arg("--target").arg("../.cargo/x86_64-tdx-deko.json");

            if release {
                cmd.arg("--release");
            } else {
                cmd.arg("--debug");
            }

            println!("Building Deko with command: {:?}", cmd);
            cmd.status().context("Failed to build Deko")?;
        }
    }
    Ok(())
}

fn qemu(config_path: &str) -> Result<()> {
    let config = match load_qemu_config(config_path) {
        Ok(cfg) => cfg,
        Err(_) => Default::default(),
    };

    println!("--- Launching QEMU ---");
    println!("Configuration: {:#?}", config);

    let mut cmd = std::process::Command::new("qemu-system-x86_64");
    cmd.args(["-accel", "kvm", "-cpu", "host"]);
    cmd.arg("-smp").arg(config.smp_cores.to_string());
    cmd.arg("-bios").arg(&config.bios_path);

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

    // TDX specific configuration
    if config.enable_tdx {
        cmd.arg("-machine").arg(format!(
            "type=q35,confidential-guest-support=tdx,kernel_irqchip=split,memory-backend=ram0"
        ));
        cmd.args(["-object", "tdx-guest,id=tdx"]);
        cmd.args(["-object", "iommufd,id=iommufd0"]);
        cmd.arg("-object").arg(format!("memory-backend-ram,id=ram0,size={}", config.memory));
    } else {
        // Standard (non-TDX) machine configuration
        cmd.arg("-machine").arg("type=q35,kernel_irqchip=split");
        cmd.arg("-m").arg(&config.memory);
    }

    println!("Executing command: {:?}", cmd);

    let mut child = cmd.spawn().context("Failed to spawn QEMU")?;
    child.wait().context("QEMU process failed")?;

    println!("Running QEMU with the following configuration:");

    Ok(())
}

fn create_bootable(loader_path: &str, deko_monitor_path: &str) -> Result<()> {
    // Logic to create a bootable image using the provided paths
    let loader_path = project_root().join(loader_path);
    let deko_monitor_path = project_root().join(deko_monitor_path);
    let boot_img_path = project_root().join("target/release/boot.img");

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
