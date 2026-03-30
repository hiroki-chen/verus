use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context, Result};
use colored::Colorize;

use crate::cli::BuildTarget;
use crate::config::{load_qemu_config, qemu_sev, qemu_tdx, ProjectConfig};

pub(crate) struct Builder {
    config: ProjectConfig,
}

impl Builder {
    pub(crate) fn new(target_arch: String) -> Self {
        Self { config: ProjectConfig::new(target_arch) }
    }

    pub(crate) fn find_verus_binary(&self) -> Result<PathBuf> {
        if let Ok(output) = Command::new("which").arg("verus").output() {
            if output.status.success() {
                let path_str = String::from_utf8_lossy(&output.stdout);
                if !path_str.is_empty() {
                    println!("✓ Found verus in PATH: {}", path_str.bright_green());
                    return Ok(PathBuf::from(path_str.to_string()));
                }
            }
        }

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

        let tools_verus = self.config.root.join("tools").join("cargo-verus");
        if tools_verus.exists() {
            println!(
                "✓ Found verus in project tools: {}",
                tools_verus.display().to_string().bright_green()
            );
            return Ok(tools_verus);
        }

        bail!(
            "Could not find verus binary. Please ensure it's in PATH, set VERUS_PATH, or run 'cargo run --bin xtask -- bootstrap-verus' first."
        );
    }

    pub(crate) fn find_z3_binary(&self) -> Result<PathBuf> {
        if let Ok(output) = Command::new("which").arg("z3").output() {
            if output.status.success() {
                let path_str = String::from_utf8_lossy(&output.stdout);
                if !path_str.is_empty() {
                    println!("✓ Found z3 in PATH: {}", path_str.bright_green());
                    return Ok(PathBuf::from(path_str.to_string()));
                }
            }
        }

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

        let tools_z3 = self.config.root.join("tools").join("z3");
        if tools_z3.exists() {
            println!(
                "✓ Found z3 in project tools: {}",
                tools_z3.display().to_string().bright_green()
            );
            return Ok(tools_z3);
        }

        bail!(
            "Could not find z3 binary. Please ensure it's in PATH, set VERUS_Z3_PATH, or run 'cargo run --bin xtask -- bootstrap-verus' first."
        );
    }

    fn find_qemu_binary(&self) -> Result<PathBuf> {
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

        let tools_qemu = self.config.root.join("tools").join("bin").join("qemu-system-x86_64");
        if tools_qemu.exists() {
            println!(
                "✓ Found QEMU in project tools: {}",
                tools_qemu.display().to_string().bright_green()
            );
            return Ok(tools_qemu);
        }

        println!("✓ Using QEMU from PATH: qemu-system-x86_64");
        Ok(PathBuf::from("qemu-system-x86_64"))
    }

    pub(crate) fn build(&self, target: BuildTarget, release: bool) -> Result<()> {
        match target {
            BuildTarget::All => {
                self.build(BuildTarget::Stage1, release)?;
                self.build(BuildTarget::Deko, release)?;
                self.build(BuildTarget::Init, release)?;
                Ok(())
            }
            BuildTarget::Deko => self.build_deko(release),
            BuildTarget::Stage1 => self.build_stage1(release),
            BuildTarget::Init => self.build_init(release),
        }
    }

    pub(crate) fn build_agent(&self, release: bool, stage: bool) -> Result<()> {
        println!("{}", "--- Building deko-agent ---".bright_cyan().bold());
        println!("\n{} Discovering required binaries...", "🔍".bright_yellow());
        let verus_binary = self.find_verus_binary()?;
        let z3_binary = self.find_z3_binary()?;

        std::env::set_var("VERUS_Z3_PATH", &z3_binary);
        std::env::set_var("RUSTC_BOOTSTRAP", "1");

        if verus_binary != PathBuf::from("verus") {
            let verus_dir = verus_binary.parent().unwrap_or_else(|| Path::new("."));
            let current_path = std::env::var("PATH").unwrap_or_default();
            let new_path = format!("{}:{}", verus_dir.display(), current_path);
            std::env::set_var("PATH", new_path);
        }

        let mut cmd = Command::new("cargo-verus");
        cmd.arg("build")
            .arg("--manifest-path")
            .arg(self.config.root.join("deko-agent").join("Cargo.toml"))
            .arg("--")
            .arg("--expand-errors");

        if release {
            cmd.arg("--release");
        }

        let profile = if release { "release" } else { "debug" };
        let log_file = format!("deko-agent-build-{}.log", profile);
        self.execute_with_logging(cmd, &log_file)?;

        let agent_root = self.config.root.join("deko-agent");
        let built_binary = self.config.root.join("target").join(profile).join("deko-agent");
        if !built_binary.exists() {
            bail!("Built deko-agent binary not found at {:?}", built_binary);
        }

        if stage {
            let dist_dir = agent_root.join("dist");
            fs::create_dir_all(&dist_dir).context("Failed to create deko-agent/dist directory")?;
            let staged_binary = dist_dir.join("deko-agent");
            fs::copy(&built_binary, &staged_binary).with_context(|| {
                format!(
                    "Failed to stage deko-agent binary from {:?} to {:?}",
                    built_binary, staged_binary
                )
            })?;
            println!(
                "{} Staged deko-agent binary to {}",
                "✓".green(),
                staged_binary.display().to_string().bright_white()
            );
        }

        println!(
            "{} Built deko-agent binary at {}",
            "✓".green(),
            built_binary.display().to_string().bright_white()
        );
        Ok(())
    }

    fn execute_cargo_with_json(&self, mut cmd: Command, _log_file_name: &str) -> Result<()> {
        println!("{} Executing command: {:?}", "→".bright_blue(), cmd);

        let status = cmd.status().context("Failed to execute command")?;
        if !status.success() {
            return Err(anyhow::anyhow!("Command failed with exit code: {}", status));
        }

        println!("{} Command completed successfully", "✓".green());
        Ok(())
    }

    fn execute_with_logging(&self, mut cmd: Command, log_file_name: &str) -> Result<()> {
        let log_dir = self.config.root.join("logs");
        fs::create_dir_all(&log_dir).context("Failed to create logs directory")?;

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
        let mut log_file = log_file;
        writeln!(log_file, "=== COMMAND ===")?;
        writeln!(log_file, "{:?}", cmd)?;
        writeln!(log_file, "\n=== STDOUT ===")?;
        log_file.write_all(&output.stdout)?;
        writeln!(log_file, "\n=== STDERR ===")?;
        log_file.write_all(&output.stderr)?;
        writeln!(log_file, "\n=== EXIT STATUS ===")?;
        writeln!(log_file, "{}", output.status)?;

        if !output.status.success() {
            println!("{} Command failed with exit code: {}", "✗".red(), output.status);
            println!("{} Check log file for details: {:?}", "📄".yellow(), log_file_path);

            let stderr_str = String::from_utf8_lossy(&output.stderr);
            let stderr_lines: Vec<&str> = stderr_str.lines().collect();
            if !stderr_lines.is_empty() {
                println!("{}", "Last few lines of stderr:".yellow());
                for line in stderr_lines.iter().rev().take(5).rev() {
                    println!("  {}", line);
                }
            }

            return Err(anyhow::anyhow!("Command failed"));
        }

        println!("{} Command completed successfully", "✓".green());

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

        Ok(())
    }

    fn build_deko(&self, release: bool) -> Result<()> {
        println!("{}", "--- Building stage2 bootloader ---".bright_cyan().bold());
        println!("\n{} Discovering required binaries...", "🔍".bright_yellow());
        let verus_binary = self.find_verus_binary()?;
        let z3_binary = self.find_z3_binary()?;

        std::env::set_var("VERUS_Z3_PATH", &z3_binary);
        std::env::set_var("RUSTC_BOOTSTRAP", "1");

        let stage2_path = self.config.root.join("bin").join("deko-stage2");
        std::env::set_current_dir(&stage2_path)
            .context("Failed to change directory to bin directory")?;

        if verus_binary != PathBuf::from("verus") {
            let verus_dir = verus_binary.parent().unwrap_or_else(|| Path::new("."));
            let current_path = std::env::var("PATH").unwrap_or_default();
            let new_path = format!("{}:{}", verus_dir.display(), current_path);
            std::env::set_var("PATH", new_path);
        }

        let mut cmd = Command::new("cargo-verus");
        cmd.arg("build")
            .arg("--features")
            .arg(&self.config.target_arch)
            .arg("--target")
            .arg(self.config.custom_target_name());
        cmd.env("RUST_TARGET_PATH", self.config.root.join(".cargo"));

        if release {
            cmd.arg("--release");
        }
        cmd.arg("--").arg("--expand-errors");

        let profile = if release { "release" } else { "debug" };
        let log_file = format!("deko-stage2-build-{}-{}.log", self.config.target_arch, profile);
        self.execute_cargo_with_json(cmd, &log_file)?;

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

        let mut cmd = Command::new("cargo");
        cmd.arg("verus")
            .arg("build")
            .arg("--features")
            .arg(&self.config.target_arch)
            .arg("--target")
            .arg(self.config.custom_target_name());
        cmd.env("RUST_TARGET_PATH", self.config.root.join(".cargo"));

        if release {
            cmd.arg("--release");
        }
        cmd.arg("--").arg("--expand-errors");

        let log_file = format!("deko-monitor-build-{}-{}.log", self.config.target_arch, profile);
        self.execute_cargo_with_json(cmd, &log_file)?;

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
        self.execute_cargo_with_json(cmd, &log_file)
    }

    fn build_init(&self, release: bool) -> Result<()> {
        println!("{}", "--- Building init binary ---".bright_cyan().bold());

        std::env::set_current_dir(&self.config.root.join("bin").join("init"))
            .context("Failed to change directory to bin/init")?;

        let mut cmd = Command::new("cargo");
        cmd.arg("-Z")
            .arg("build-std=core,compiler_builtins")
            .arg("-Z")
            .arg("build-std-features=compiler-builtins-mem")
            .arg("build")
            .arg("--package")
            .arg("init")
            .arg("--target")
            .arg(self.config.custom_target_name());
        cmd.env("RUST_TARGET_PATH", self.config.root.join(".cargo"));

        if release {
            cmd.arg("--release");
        }

        let profile = if release { "release" } else { "debug" };
        let log_file = format!("init-build-{}.log", profile);
        self.execute_cargo_with_json(cmd, &log_file)?;

        println!("✓ Init binary built successfully");
        Ok(())
    }

    fn prepare_qemu_command(&self, config_path: Option<PathBuf>) -> Result<Command> {
        let config_path = config_path.unwrap_or_else(|| self.config.qemu_config_path());

        let config = match load_qemu_config(&config_path) {
            Ok(cfg) => cfg,
            Err(e) => {
                println!("Warning: Failed to load config ({}), using defaults", e);
                Default::default()
            }
        };

        let qemu_binary = self.find_qemu_binary()?;
        let mut cmd = Command::new(qemu_binary);

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
        }

        cmd.args(["-accel", "kvm"]);
        cmd.arg("-smp").arg(config.smp_cores.to_string());

        for (i, drive) in config.drive.iter().enumerate() {
            cmd.arg("-drive").arg(format!(
                "file={},if={},format={},id=disk{}",
                drive.file.display(),
                drive.interface,
                drive.format,
                i
            ));
        }

        if !config.enable_graphics {
            cmd.args(["-nographic", "-vga", "none"]);
        }

        cmd.args(["-nodefaults", "-no-reboot"]);

        if config.enable_cvm {
            match self.config.target_arch.as_str() {
                "snp" => qemu_sev(&config, &mut cmd),
                "tdx" => qemu_tdx(&config, &mut cmd),
                _ => bail!("Unsupported target architecture: {}", self.config.target_arch),
            }
        }

        if config.debug {
            cmd.arg("-s");
        }

        for extra in &config.extra_config {
            cmd.arg(extra);
        }

        Ok(cmd)
    }

    pub(crate) fn qemu(&self, config_path: Option<PathBuf>) -> Result<()> {
        let mut cmd = self.prepare_qemu_command(config_path)?;
        println!("✓ Launching QEMU");
        println!("✓ Executing command: {:?}", cmd);

        let mut child = cmd.spawn().context("Failed to spawn QEMU")?;
        child.wait().context("QEMU process failed")?;
        Ok(())
    }

    pub(crate) fn stress_test(
        &self,
        iter: usize,
        timeout: u64,
        config_path: Option<PathBuf>,
    ) -> Result<()> {
        use std::io::{BufRead, BufReader};
        use std::sync::mpsc;
        use std::thread;
        use std::time::Duration;

        println!("{} Starting QEMU stress test", "🧪".bright_cyan().bold());
        println!("Iterations: {}", iter);
        println!("Timeout per run: {}s", timeout);

        let mut passed = 0;
        let mut failed = 0;

        for i in 1..=iter {
            print!("Iteration {}/{}: ", i, iter);
            std::io::stdout().flush()?;

            let mut cmd = self.prepare_qemu_command(config_path.clone())?;
            cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

            let mut child = cmd.spawn().context("Failed to spawn QEMU")?;
            let stdout = child.stdout.take().unwrap();
            let (tx, rx) = mpsc::channel::<bool>();

            let tx_clone = tx.clone();
            thread::spawn(move || {
                let reader = BufReader::new(stdout);
                for line in reader.lines() {
                    match line {
                        Ok(l) => {
                            if l.contains("SecCoreStartupWithStack(0xFFFCC000, 0x820000)") {
                                let _ = tx_clone.send(true);
                                break;
                            }
                            if l.contains("invalid argument") {
                                let _ = tx_clone.send(false);
                                break;
                            }
                        }
                        Err(_) => break,
                    }
                }
            });

            match rx.recv_timeout(Duration::from_secs(timeout)) {
                Ok(true) => {
                    println!("{}", "PASSED".green());
                    passed += 1;
                }
                Ok(false) => {
                    println!("{}", "FAILED (invalid argument)".red());
                    failed += 1;
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    println!("{}", "FAILED (timeout)".red());
                    failed += 1;
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    println!("{}", "FAILED (process exited early)".red());
                    failed += 1;
                }
            }

            let _ = child.kill();
            let _ = child.wait();
        }

        println!("\n{}", "═".repeat(60));
        println!("Total: {}", iter);
        println!("Passed: {}", passed.to_string().green());
        println!("Failed: {}", failed.to_string().red());

        if failed > 0 {
            bail!("Stress test failed with {} errors", failed);
        }

        Ok(())
    }

    pub(crate) fn create_bootable(
        &self,
        ovmf_path: Option<PathBuf>,
        stage2_path: Option<PathBuf>,
        stage1_path: Option<PathBuf>,
        release: bool,
    ) -> Result<()> {
        match self.config.target_arch.as_str() {
            "snp" => self.create_bootable_snp(ovmf_path, stage2_path, release),
            "tdx" => self.create_bootable_tdx(stage2_path, stage1_path, release),
            _ => bail!("Unsupported target architecture: {}", self.config.target_arch),
        }
    }

    fn create_bootable_tdx(
        &self,
        deko_monitor_path: Option<PathBuf>,
        stage1_path: Option<PathBuf>,
        release: bool,
    ) -> Result<()> {
        self.build(BuildTarget::All, release)?;

        let loader_path = stage1_path.unwrap_or_else(|| self.config.stage1_path(release));
        let deko_monitor_path =
            deko_monitor_path.unwrap_or_else(|| self.config.deko_monitor_path(release));
        let boot_img_path = self.config.boot_image_path(release);

        println!("✓ Creating bootable image with:");
        println!("  Loader Path: {:?}", loader_path);
        println!("  Deko Monitor Path: {:?}", deko_monitor_path);
        println!("  Boot Image Path: {:?}", boot_img_path);

        let img_file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(&boot_img_path)
            .context("Failed to create or open boot image file")?;

        let img_len = 1024 * 1024 * 64;
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
        release: bool,
    ) -> Result<()> {
        let stage2_path = stage2_path.unwrap_or_else(|| self.config.stage2_binary_path(release));
        let boot_img_path = self.config.igvm_path(release);
        let ovmf_path = ovmf_path.unwrap_or_else(ProjectConfig::default_ovmf_path);
        let kernel_path = self.config.deko_monitor_path(release);

        println!("✓ Creating IGVM image with:");
        println!("  Stage2 Path: {:?}", stage2_path);
        println!("  Kernel Path: {:?}", kernel_path);
        println!("  OVMF Path: {:?}", ovmf_path);
        println!("  Output: {:?}", boot_img_path);

        let mut cmd = Command::new("igvmbuilder");
        cmd.args(["--sort", "--policy", "0x30001", "--snp"]);
        cmd.args(["--firmware", &ovmf_path.display().to_string()]);
        cmd.args(["--stage2", &stage2_path.display().to_string()]);
        cmd.args(["--kernel", &kernel_path.display().to_string()]);
        cmd.args(["--output", &boot_img_path.display().to_string()]);
        cmd.arg("qemu");

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
