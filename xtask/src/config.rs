use std::fs;
use std::path::{Path, PathBuf};

use anyhow::Result;
use serde::Deserialize;

use crate::util::project_root;

const DEFAULT_MEMORY: &str = "4G";
const DEFAULT_SMP_CORES: u32 = 4;

#[derive(Debug)]
pub(crate) struct ProjectConfig {
    pub(crate) root: PathBuf,
    pub(crate) target_arch: String,
    target_triple: String,
}

impl ProjectConfig {
    pub(crate) fn new(target_arch: String) -> Self {
        let root = project_root();
        let target_triple = format!("x86_64-{}-deko", target_arch);

        Self { root, target_arch, target_triple }
    }

    pub(crate) fn target_dir(&self, release: bool) -> PathBuf {
        let profile = if release { "release" } else { "debug" };
        self.root.join("target").join(&self.target_triple).join(profile)
    }

    pub(crate) fn stage1_path(&self, release: bool) -> PathBuf {
        let profile = if release { "release" } else { "debug" };
        self.root.join("target").join("x86_64-unknown-uefi").join(profile).join("deko-stage1.efi")
    }

    pub(crate) fn deko_monitor_path(&self, release: bool) -> PathBuf {
        self.target_dir(release).join("deko")
    }

    pub(crate) fn stage2_binary_path(&self, release: bool) -> PathBuf {
        self.target_dir(release).join("deko-stage2.bin")
    }

    pub(crate) fn stage2_path(&self, release: bool) -> PathBuf {
        self.target_dir(release).join("stage2")
    }

    pub(crate) fn deko_elf_path(&self, release: bool) -> PathBuf {
        self.target_dir(release).join("deko.elf")
    }

    pub(crate) fn boot_image_path(&self, release: bool) -> PathBuf {
        self.target_dir(release).join("boot.img")
    }

    pub(crate) fn igvm_path(&self, release: bool) -> PathBuf {
        self.target_dir(release).join("igvm.igvm")
    }

    pub(crate) fn custom_target_name(&self) -> &str { &self.target_triple }

    pub(crate) fn default_ovmf_path() -> PathBuf {
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

        dirs::home_dir()
            .map(|d| d.join(".local/share/ovmf/OVMF.fd"))
            .unwrap_or_else(|| PathBuf::from("~/.local/share/ovmf/OVMF.fd"))
    }

    pub(crate) fn qemu_config_path(&self) -> PathBuf { self.root.join(".config/qemu.config.toml") }
}

#[derive(Debug)]
pub(crate) struct FinalQemuConfig {
    pub(crate) memory: String,
    pub(crate) smp_cores: u32,
    pub(crate) enable_cvm: bool,
    pub(crate) enable_graphics: bool,
    pub(crate) drive: Vec<DriveConfig>,
    pub(crate) debug: bool,
    pub(crate) igvm_path: String,
    pub(crate) bios_path: String,
    pub(crate) extra_config: Vec<String>,
}

#[derive(Debug, Deserialize, Clone)]
pub(crate) struct DriveConfig {
    pub(crate) file: PathBuf,
    pub(crate) format: String,
    pub(crate) interface: String,
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

impl Default for FinalQemuConfig {
    fn default() -> Self {
        let config = ProjectConfig::new("snp".to_string());

        Self {
            memory: DEFAULT_MEMORY.to_string(),
            smp_cores: DEFAULT_SMP_CORES,
            enable_cvm: true,
            enable_graphics: false,
            drive: vec![],
            debug: false,
            igvm_path: config.igvm_path(false).display().to_string(),
            bios_path: ProjectConfig::default_ovmf_path().display().to_string(),
            extra_config: vec![],
        }
    }
}

pub(crate) fn load_qemu_config(path: &Path) -> Result<FinalQemuConfig> {
    let mut config = FinalQemuConfig::default();

    if !path.exists() {
        return Err(anyhow::anyhow!("Config file not found: {:?}", path));
    }

    println!("✓ Loading QEMU configuration from: {:?}", path);

    let content = fs::read_to_string(path)?;
    let partial = toml::from_str::<PartialQemuConfig>(&content)?;

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

pub(crate) fn qemu_sev(config: &FinalQemuConfig, cmd: &mut std::process::Command) {
    cmd.arg("-machine").arg(
        "type=q35,confidential-guest-support=sev,kernel_irqchip=split,igvm-cfg=igvm,memory-backend=ram",
    );
    cmd.args(["-object", "sev-snp-guest,id=sev,reduced-phys-bits=1,cbitpos=51"]);
    cmd.arg("-object").arg(format!("memory-backend-memfd,id=ram,size={}", config.memory));
    cmd.arg("-object").arg(format!("igvm-cfg,id=igvm,file={}", config.igvm_path));
}

pub(crate) fn qemu_tdx(config: &FinalQemuConfig, cmd: &mut std::process::Command) {
    cmd.arg("-machine")
        .arg("type=q35,confidential-guest-support=tdx,kernel_irqchip=split,memory-backend=ram0");

    let tdx_arg = if config.debug { "tdx-guest,id=tdx,debug=on" } else { "tdx-guest,id=tdx" };

    cmd.args(["-object", tdx_arg]);
    cmd.args(["-object", "iommufd,id=iommufd0"]);
    cmd.arg("-object").arg(format!("memory-backend-ram,id=ram0,size={}", config.memory));
    cmd.args(["-bios", &config.bios_path]);
}
