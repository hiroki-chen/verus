use std::fs::{self};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand, ValueEnum};
use serde::Deserialize;

const DEFAULT_OVMF_PATH: &str = "~/.local/share/ovmf/OVMF.fd";
const DEFAULT_DEKO_MONITOR_PATH: &str = "target/x86_64-sev-deko/release/deko-monitor";

#[derive(Debug)]
struct FinalQemuConfig {
    memory: String,
    smp_cores: u32,
    enable_sev: bool,
    enable_graphics: bool, // Unified graphic/nographic switch
    drive: Vec<DriveConfig>,
    debug: bool,
    igvm_path: String,
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
    enable_tdx: Option<bool>,
    enable_graphics: Option<bool>,
    drive: Option<Vec<DriveConfig>>,
    debug: Option<bool>,
    igvm_path: Option<String>,
}

#[derive(ValueEnum, Debug, Clone)]
enum BuildTarget {
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
        ovmf_path: Option<String>,
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
            enable_sev: true,
            enable_graphics: false, // Default to nographic
            drive: vec![],
            igvm_path: project_root().join("target/release/boot.igvm").display().to_string(),
            debug: false,
        }
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::CreateBootable { ovmf_path, deko_monitor_path } => {
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

            create_bootable(
                ovmf_path.as_deref().unwrap_or(DEFAULT_OVMF_PATH),
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
                project_root().join(".config/qemu.config.toml").display().to_string()
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
    if let Some(tdx) = partial.enable_tdx {
        config.enable_sev = tdx;
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

fn build(target: BuildTarget, release: bool) -> Result<()> {
    match target {
        BuildTarget::Deko => {
            // Change the working directory to the deko-monitor package
            let deko_core_path = project_root().join("deko-monitor");
            std::env::set_current_dir(&deko_core_path)
                .context("Failed to change directory to deko-monitor")?;
            let mut cmd = std::process::Command::new("cargo");
            cmd.arg("verus").arg("build").arg("--target").arg("../.cargo/x86_64-sev-deko.json");

            if release {
                cmd.arg("--release");
            } else {
                cmd.arg("--debug");
            }

            println!("Building Deko with command: {:?}", cmd);
            if !cmd.status()?.success() {
                bail!("Cannot build deko");
            }

            Ok(())
        }
    }
}

fn qemu(config_path: &str) -> Result<()> {
    let config = match load_qemu_config(config_path) {
        Ok(cfg) => cfg,
        Err(_) => Default::default(),
    };

    println!("--- Launching QEMU ---");
    println!("Configuration: {:#?}", config);

    let mut cmd = std::process::Command::new("qemu-system-x86_64");
    cmd.args(["-accel", "kvm", "-cpu", "EPYC-v4,host-phys-bits=true"]);
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

    // SEV specific configuration
    if config.enable_sev {
        cmd.arg("-machine").arg(format!(
            "type=q35,confidential-guest-support=sev,kernel_irqchip=split,igvm-cfg=igvm,memory-backend=ram"
        ));

        cmd.args(["-object", "sev-snp-guest,id=sev,reduced-phys-bits=1,cbitpos=51"]);
        cmd.arg("-object").arg(format!("memory-backend-memfd,id=ram,size={}", config.memory));
        cmd.arg("-object").arg(format!("igvm-cfg,id=igvm,file={}", config.igvm_path));
    } else {
        // Standard (non-SEV) machine configuration
        cmd.arg("-machine").arg("type=q35,kernel_irqchip=split");
        cmd.arg("-m").arg(&config.memory);
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

/// TODO: For SEV we can use IGVM file format so there is no need to support legacy EFI.
fn create_bootable(ovmf_path: &str, deko_monitor_path: &str) -> Result<()> {
    // First ensure that our package is fresh.
    build(BuildTarget::Deko, true)?;

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
    cmd.args(["--stage2", deko_monitor_path.to_str().unwrap()]);
    // TODO: Now a placeholder.
    cmd.args(["--kernel", deko_monitor_path.to_str().unwrap()]);
    cmd.args(["--output", boot_img_path.to_str().unwrap()]);
    cmd.arg("qemu");

    println!("Executing command: {:?}", cmd);

    let mut child = cmd.spawn().context("Failed to spawn igvmbuilder")?;
    child.wait().context("igvmbuilder process failed")?;

    println!("--- IGVM Image created at {:?} ---", boot_img_path);
    Ok(())
}
