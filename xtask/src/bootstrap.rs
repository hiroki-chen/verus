use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::{bail, Context, Result};
use colored::Colorize;
use git2::Repository;

use crate::util::{copy_dir_recursive, project_root};

pub(crate) fn bootstrap_ovmf() -> Result<()> {
    println!("{} Bootstrapping OVMF with COCONUT-SVSM support...", "→".bright_cyan());

    let project_root = project_root();
    let build_dir = project_root.join("/tmp");
    let tools_dir = project_root.join("tools");
    let share_dir = tools_dir.join("share");

    println!("Build directory: {}", build_dir.display().to_string().bright_white());
    println!("Installation destination: {}", share_dir.display().to_string().bright_white());

    std::fs::create_dir_all(&build_dir).context("Failed to create build directory")?;
    std::fs::create_dir_all(&share_dir).context("Failed to create tools/share directory")?;

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

    println!("\n{} Checking out svsm branch...", "🌿".bright_green());
    std::env::set_current_dir(&edk2_dir).context("Failed to change to EDK2 directory")?;

    let branch_name = "svsm";
    println!("Checking out {} branch...", branch_name);

    let mut remote = repo.find_remote("origin").context("Failed to find origin remote")?;
    remote
        .fetch(&["refs/heads/*:refs/remotes/origin/*"], None, None)
        .context("Failed to fetch from origin")?;

    let remote_branch_name = format!("origin/{}", branch_name);
    let (object, _) = repo
        .revparse_ext(&remote_branch_name)
        .with_context(|| format!("Failed to find remote branch {}", remote_branch_name))?;

    repo.checkout_tree(&object, None)?;

    let branch_ref_name = format!("refs/heads/{}", branch_name);
    if repo.find_reference(&branch_ref_name).is_ok() {
        repo.set_head(&branch_ref_name)?;
    } else {
        repo.reference(&branch_ref_name, object.id(), false, "checkout remote branch")?;
        repo.set_head(&branch_ref_name)?;
    }

    println!("✓ Checked out branch: {}", branch_name);

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

    println!("\n{} Setting up environment variables...", "⚙️".bright_cyan());
    std::env::set_var("PYTHON3_ENABLE", "TRUE");
    std::env::set_var("PYTHON_COMMAND", "python3");
    println!("✓ Set PYTHON3_ENABLE=TRUE");
    println!("✓ Set PYTHON_COMMAND=python3");

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

    println!("\n{} Cleaning up build directory...", "🧹".bright_cyan());
    if edk2_dir.exists() {
        std::fs::remove_dir_all(&edk2_dir).context("Failed to remove EDK2 build directory")?;
        println!("✓ Removed EDK2 build directory");
    }

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

pub(crate) fn bootstrap_qemu() -> Result<()> {
    println!("{} Bootstrapping QEMU with IGVM support...", "→".bright_cyan());

    let project_root = project_root();
    let tools_dir = project_root.join("tools");
    let build_dir = project_root.join("/tmp");

    println!("Installation directory: {}", tools_dir.display().to_string().bright_white());

    std::fs::create_dir_all(&build_dir).context("Failed to create build directory")?;
    std::fs::create_dir_all(&tools_dir).context("Failed to create tools directory")?;

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
        if stderr.contains("already exists") || stdout.contains("already installed") {
            println!("✓ cargo-c already installed");
        } else {
            bail!("Failed to install cargo-c:\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
        }
    } else {
        println!("✓ cargo-c installed successfully");
    }

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

    std::env::set_current_dir(&igvm_dir).context("Failed to change to IGVM directory")?;
    println!("Checking IGVM repository structure...");
    println!("Installing IGVM library to: {}", igvm_install_dir.display());

    std::fs::create_dir_all(&igvm_install_dir).context("Failed to create tools/lib directory")?;

    let igvm_c_dir = igvm_dir.join("igvm_c");
    if !igvm_c_dir.exists() {
        bail!("IGVM repository structure is not as expected - igvm_c directory not found");
    }

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

    let include_src_dir = igvm_dir.join("igvm_c").join("include");
    let include_dest_dir = igvm_install_dir.join("include/igvm");

    if include_src_dir.exists() {
        std::fs::create_dir_all(&include_dest_dir).context("Failed to create include directory")?;

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

    let repo = Repository::open(&qemu_dir).context("Failed to open QEMU repository")?;
    let branch_name = "svsm-igvm";
    println!("Checking out {} branch...", branch_name);

    let mut remote = repo.find_remote("origin").context("Failed to find origin remote")?;
    remote
        .fetch(&["refs/heads/*:refs/remotes/origin/*"], None, None)
        .context("Failed to fetch from origin")?;

    let remote_branch_name = format!("origin/{}", branch_name);
    let (object, _) = repo
        .revparse_ext(&remote_branch_name)
        .with_context(|| format!("Failed to find remote branch {}", remote_branch_name))?;

    repo.checkout_tree(&object, None)?;

    let branch_ref_name = format!("refs/heads/{}", branch_name);
    if repo.find_reference(&branch_ref_name).is_ok() {
        repo.set_head(&branch_ref_name)?;
    } else {
        repo.reference(&branch_ref_name, object.id(), false, "checkout remote branch")?;
        repo.set_head(&branch_ref_name)?;
    }

    println!("✓ Checked out branch: {}", branch_name);

    std::env::set_current_dir(&qemu_dir).context("Failed to change to QEMU directory")?;

    let qemu_install_dir = tools_dir.clone();
    println!("Configuring QEMU...");
    println!("  QEMU install directory: {}", qemu_install_dir.display());

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
        .arg("--enable-igvm")
        .arg("--enable-slirp")
        .arg("--enable-vhost-net");

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

    println!("Installing QEMU to tools/bin...");
    let mut cmd = Command::new("make");
    cmd.arg("install");

    let output = cmd.output().context("Failed to install QEMU")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Failed to install QEMU:\n{}", stderr);
    }

    println!("✓ QEMU installed successfully");

    println!("\n{} Cleaning up build directories...", "🧹".bright_cyan());

    if igvm_dir.exists() {
        std::fs::remove_dir_all(&igvm_dir).context("Failed to remove IGVM build directory")?;
        println!("✓ Removed IGVM build directory");
    }
    if qemu_dir.exists() {
        std::fs::remove_dir_all(&qemu_dir).context("Failed to remove QEMU build directory")?;
        println!("✓ Removed QEMU build directory");
    }

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

pub(crate) fn bootstrap_verus(
    prefix: &Path,
    commit: Option<&str>,
    branch: Option<&str>,
) -> Result<()> {
    println!("{} Bootstrapping Verus from source...", "→".bright_cyan());
    println!("Installation prefix: {}", prefix.display().to_string().bright_white());

    std::fs::create_dir_all(prefix).context("Failed to create prefix directory")?;

    let verus_dir = prefix.join("verus");

    println!("\n{} Cloning Verus repository...", "🔀".bright_yellow());

    if verus_dir.exists() {
        println!("🗑 Removing existing verus directory...");
        std::fs::remove_dir_all(&verus_dir).context("Failed to remove existing verus directory")?;
    }

    let repo_url = "https://github.com/verus-lang/verus.git";
    println!("Cloning from: {}", repo_url.bright_blue());

    let repo =
        Repository::clone(repo_url, &verus_dir).context("Failed to clone Verus repository")?;

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

            let mut remote = repo.find_remote("origin").context("Failed to find origin remote")?;
            remote
                .fetch(&["refs/heads/*:refs/remotes/origin/*"], None, None)
                .context("Failed to fetch from origin")?;

            let remote_branch_name = format!("origin/{}", branch_name);
            let (object, _) = repo
                .revparse_ext(&remote_branch_name)
                .with_context(|| format!("Failed to find remote branch {}", remote_branch_name))?;

            repo.checkout_tree(&object, None)?;

            let branch_ref_name = format!("refs/heads/{}", branch_name);
            if repo.find_reference(&branch_ref_name).is_ok() {
                repo.set_head(&branch_ref_name)?;
            } else {
                repo.reference(&branch_ref_name, object.id(), false, "checkout remote branch")?;
                repo.set_head(&branch_ref_name)?;
            }

            println!("✓ Checked out branch: {}", branch_name);
        }
        (Some(_), Some(_)) => bail!("Cannot specify both commit and branch - please choose one"),
        (None, None) => println!("✓ Using default branch"),
    }

    println!("✓ Repository cloned successfully!");

    let verus_toolchain_path = verus_dir.join("rust-toolchain.toml");
    std::env::set_current_dir(&verus_dir).context("Failed to change to verus directory")?;
    println!("✓ Changed to verus directory: {}", verus_dir.display().to_string().bright_white());

    let rust_version = if verus_toolchain_path.exists() {
        let toolchain_content = std::fs::read_to_string(&verus_toolchain_path)
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

    println!("\n{} Checking rustup installation...", "🦀".bright_yellow());
    let rustup_check = Command::new("rustup").arg("--version").output();
    match rustup_check {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("✓ Found rustup: {}", version.trim().bright_white());
        }
        _ => bail!("rustup not found. Please install rustup from https://rustup.rs first."),
    }

    println!("✓ rustup is installed.");

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

    println!("\n{} Building Verus using vargo...", "🚀".bright_green());
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

    println!("\n{} Copying Verus binaries to project tools directory...", "📦".bright_cyan());

    let verus_target_path = source_dir.join("target/release");
    let project_tools_dir = project_root().join("tools");

    println!("Source directory: {}", verus_target_path.display().to_string().bright_white());
    println!("Destination directory: {}", project_tools_dir.display().to_string().bright_white());

    std::fs::create_dir_all(&project_tools_dir).context("Failed to create tools directory")?;

    copy_dir_recursive(&verus_target_path, &project_tools_dir)
        .context("Failed to copy Verus built files to tools directory")?;

    let z3_path = source_dir.join("z3");
    if z3_path.exists() {
        println!("Copying Z3 binary...");
        let z3_dest = project_tools_dir.join("z3");
        std::fs::copy(&z3_path, &z3_dest).context("Failed to copy Z3 binary")?;

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

    println!("\n{} Finalizing bootstrap setup...", "🔧".bright_cyan());

    if verus_dir.exists() {
        std::fs::remove_dir_all(&verus_dir)
            .context("Failed to delete temporary verus build directory")?;
        println!("✓ Deleted temporary build directory: {}", verus_dir.display());
    }

    let verusroot_file = project_tools_dir.join("verus-root");
    std::fs::File::create(&verusroot_file).context("Failed to create verus-root marker file")?;
    println!("✓ Created verusroot marker file at: {}", verusroot_file.display());

    println!("\n=== Verus bootstrap completed successfully! ===");

    Ok(())
}
