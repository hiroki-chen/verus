mod bootstrap;
mod builder;
mod cli;
mod config;
mod tasks;
mod util;

use anyhow::Result;
use clap::Parser;

use crate::bootstrap::{bootstrap_ovmf, bootstrap_qemu, bootstrap_verus};
use crate::builder::Builder;
use crate::cli::{Cli, Commands, TargetArch};
use crate::tasks::{line_count, pretty, test_runner};
use crate::util::project_root;

fn main() -> Result<()> {
    let cli = Cli::parse();
    let target_arch = match cli.target_arch.unwrap_or(TargetArch::Init) {
        TargetArch::Tdx => "tdx",
        TargetArch::Snp => "snp",
        TargetArch::Init => "init",
    };

    let builder = Builder::new(target_arch.to_string());

    match cli.command {
        Commands::CreateBootable { ovmf_path, stage2_path, stage1_path } => {
            builder.create_bootable(ovmf_path, stage2_path, stage1_path)
        }
        Commands::Qemu { config_path } => builder.qemu(config_path),
        Commands::StressTest { iter, timeout, config_path } => {
            builder.stress_test(iter, timeout, config_path)
        }
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
