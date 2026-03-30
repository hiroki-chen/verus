use std::path::PathBuf;

use clap::{Parser, Subcommand, ValueEnum};

#[derive(ValueEnum, Debug, Clone)]
pub(crate) enum BuildTarget {
    Deko,
    Stage1,
    Init,
    All,
}

#[derive(ValueEnum, Debug, Clone)]
pub(crate) enum TargetArch {
    Tdx,
    Snp,
    Init,
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub(crate) struct Cli {
    #[command(subcommand)]
    pub(crate) command: Commands,
    #[arg(long, value_enum, global = true)]
    pub(crate) target_arch: Option<TargetArch>,
}

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    CreateBootable {
        #[arg(short, long)]
        ovmf_path: Option<PathBuf>,
        #[arg(short, long)]
        stage2_path: Option<PathBuf>,
        #[arg(short, long)]
        stage1_path: Option<PathBuf>,
        #[arg(short, long, help = "Create a bootable image from release artifacts")]
        release: bool,
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
    BuildAgent {
        #[arg(short, long)]
        release: bool,
        #[arg(long, default_value_t = true)]
        stage: bool,
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
    StressTest {
        #[arg(short, long, default_value = "10")]
        iter: usize,
        #[arg(short = 'T', long, default_value = "30")]
        timeout: u64,
        #[arg(short, long)]
        config_path: Option<PathBuf>,
    },
}
