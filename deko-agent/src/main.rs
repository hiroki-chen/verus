mod ioctl;
mod policy_compile;

use std::fs::{self, File};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::Duration;
use std::{env, thread};

use ioctl::{bind_domain, load_policy, lookup_domain, unbind_domain};
use policy_compile::compile_policy_toml_to_blob;
use reqwest::blocking::Client;
use reqwest::Certificate;
use serde::Deserialize;
use sha2::{Digest, Sha256};

const DEFAULT_TOKEN_PATH: &str = "/var/run/secrets/kubernetes.io/serviceaccount/token";
const DEFAULT_CA_PATH: &str = "/var/run/secrets/kubernetes.io/serviceaccount/ca.crt";
const DEFAULT_KUBE_HOST: &str = "kubernetes.default.svc";
const DEFAULT_KUBE_PORT: &str = "443";

#[derive(Clone, Debug)]
struct ScanConfig {
    node_name: String,
    device_path: String,
    proc_root: PathBuf,
    bindings_file: Option<PathBuf>,
    token_path: PathBuf,
    ca_path: PathBuf,
    interval_sec: u64,
    auto_load_policy: bool,
    policy_configmap_prefix: String,
    policy_configmap_key: String,
    ready_dir: PathBuf,
}

#[derive(Clone, Debug)]
struct BindingRecord {
    namespace: String,
    pod: String,
    uid: String,
    data_storage: String,
    domain_id: u32,
    container_id: String,
    pid: u32,
    mnt_ns_id: u64,
}

#[derive(Default, Deserialize)]
struct PodList {
    items: Vec<Pod>,
}

#[derive(Default, Deserialize)]
struct Pod {
    metadata: Metadata,
    spec: PodSpec,
    status: PodStatus,
}

#[derive(Default, Deserialize)]
struct Metadata {
    name: Option<String>,
    namespace: Option<String>,
    uid: Option<String>,
    labels: Option<std::collections::BTreeMap<String, String>>,
}

#[derive(Default, Deserialize)]
struct PodSpec {
    #[serde(rename = "nodeName")]
    node_name: Option<String>,
}

#[derive(Default, Deserialize)]
struct PodStatus {
    #[serde(rename = "containerStatuses")]
    container_statuses: Option<Vec<ContainerStatus>>,
}

#[derive(Clone, Default, Deserialize)]
struct ContainerStatus {
    #[serde(rename = "containerID")]
    container_id: Option<String>,
}

#[derive(Default, Deserialize)]
struct ConfigMap {
    data: Option<std::collections::BTreeMap<String, String>>,
}

fn print_usage() {
    eprintln!(
        "usage:
  deko-agent scan [--once]
  deko-agent compile-policy --input <policy.toml> --output <policy.bin>
  deko-agent load-policy --device <path> --domain-id <u32> --policy-file <policy.toml|policy.bin> [--binary]
  deko-agent bind --device <path> --mnt-ns-id <u64> --domain-id <u32>
  deko-agent lookup --device <path> --mnt-ns-id <u64>
  deko-agent unbind --device <path> --mnt-ns-id <u64> --domain-id <u32>"
    );
}

fn parse_flag(args: &[String], flag: &str) -> Result<String, String> {
    let idx = args
        .iter()
        .position(|arg| arg == flag)
        .ok_or_else(|| format!("missing required flag {flag}"))?;
    args.get(idx + 1).cloned().ok_or_else(|| format!("missing value for {flag}"))
}

fn has_flag(args: &[String], flag: &str) -> bool { args.iter().any(|arg| arg == flag) }

fn log(message: &str) {
    println!("[deko-agent] {message}");
}

fn parse_u32_flag(args: &[String], flag: &str) -> Result<u32, String> {
    parse_flag(args, flag)?.parse::<u32>().map_err(|err| format!("invalid {flag}: {err}"))
}

fn parse_u64_flag(args: &[String], flag: &str) -> Result<u64, String> {
    parse_flag(args, flag)?.parse::<u64>().map_err(|err| format!("invalid {flag}: {err}"))
}

fn read_trimmed(path: &Path) -> Result<String, String> {
    fs::read_to_string(path)
        .map_err(|err| format!("failed to read {}: {err}", path.display()))
        .map(|text| text.trim().to_string())
}

fn stable_domain_id(data_storage: &str) -> u32 {
    let mut hasher = Sha256::new();
    hasher.update(data_storage.as_bytes());
    let digest = hasher.finalize();
    u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]])
}

fn kube_api_url() -> String {
    let host =
        env::var("KUBERNETES_SERVICE_HOST").unwrap_or_else(|_| DEFAULT_KUBE_HOST.to_string());
    let port =
        env::var("KUBERNETES_SERVICE_PORT").unwrap_or_else(|_| DEFAULT_KUBE_PORT.to_string());
    format!("https://{host}:{port}")
}

fn kube_client(config: &ScanConfig) -> Result<(Client, String), String> {
    let token = read_trimmed(&config.token_path)?;
    let ca_bytes = fs::read(&config.ca_path)
        .map_err(|err| format!("failed to read {}: {err}", config.ca_path.display()))?;
    let cert = Certificate::from_pem(&ca_bytes)
        .map_err(|err| format!("failed to parse {}: {err}", config.ca_path.display()))?;
    let client = Client::builder()
        .use_rustls_tls()
        .add_root_certificate(cert)
        .build()
        .map_err(|err| format!("failed to build kube client: {err}"))?;
    Ok((client, token))
}

fn kube_get_json<T: for<'de> Deserialize<'de>>(
    config: &ScanConfig,
    path: &str,
) -> Result<T, String> {
    let (client, token) = kube_client(config)?;
    let url = format!("{}{}", kube_api_url(), path);
    client
        .get(url)
        .bearer_auth(token)
        .send()
        .and_then(|resp| resp.error_for_status())
        .map_err(|err| format!("kube GET {path} failed: {err}"))?
        .json::<T>()
        .map_err(|err| format!("kube decode {path} failed: {err}"))
}

fn fetch_local_node_pods(config: &ScanConfig) -> Result<Vec<Pod>, String> {
    let selector = format!("spec.nodeName={}", config.node_name);
    let path = format!("/api/v1/pods?fieldSelector={selector}");
    Ok(kube_get_json::<PodList>(config, &path)?.items)
}

fn fetch_policy_bytes(
    config: &ScanConfig,
    namespace: &str,
    data_storage: &str,
) -> Result<Vec<u8>, String> {
    let configmap_name = format!("{}{}", config.policy_configmap_prefix, data_storage);
    let path = format!("/api/v1/namespaces/{namespace}/configmaps/{configmap_name}");
    let configmap = kube_get_json::<ConfigMap>(config, &path)?;
    let value = configmap
        .data
        .as_ref()
        .and_then(|data| data.get(&config.policy_configmap_key))
        .ok_or_else(|| {
            format!(
                "configmap {namespace}/{configmap_name} missing key {}",
                config.policy_configmap_key
            )
        })?;
    Ok(value.as_bytes().to_vec())
}

fn list_numeric_pids(proc_root: &Path) -> Result<Vec<u32>, String> {
    let mut pids = Vec::new();
    for entry in fs::read_dir(proc_root)
        .map_err(|err| format!("failed to read {}: {err}", proc_root.display()))?
    {
        let entry =
            entry.map_err(|err| format!("failed to walk {}: {err}", proc_root.display()))?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if let Ok(pid) = name.parse::<u32>() {
            pids.push(pid);
        }
    }
    pids.sort_unstable();
    Ok(pids)
}

fn pid_matches_container(proc_root: &Path, pid: u32, container_id: &str) -> bool {
    let cgroup_path = proc_root.join(pid.to_string()).join("cgroup");
    let Ok(text) = fs::read_to_string(cgroup_path) else {
        return false;
    };
    let short_id = &container_id[..container_id.len().min(12)];
    text.contains(container_id) || text.contains(short_id)
}

fn resolve_container_pid(proc_root: &Path, container_id: &str) -> Result<u32, String> {
    for pid in list_numeric_pids(proc_root)? {
        if pid_matches_container(proc_root, pid, container_id) {
            return Ok(pid);
        }
    }
    Err(format!("unable to resolve pid for container {container_id}"))
}

fn read_mnt_ns_id(proc_root: &Path, pid: u32) -> Result<u64, String> {
    let path = proc_root.join(pid.to_string()).join("ns").join("mnt");
    fs::metadata(&path)
        .map_err(|err| format!("failed to stat {}: {err}", path.display()))
        .map(|meta| meta.ino())
}

fn binding_key(binding: &BindingRecord) -> String {
    format!("{}:{}:{}", binding.container_id, binding.mnt_ns_id, binding.domain_id)
}

fn append_binding(path: &Path, binding: &BindingRecord) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .map_err(|err| format!("failed to mkdir {}: {err}", parent.display()))?;
    }
    let mut record = serde_json::Map::new();
    record.insert("namespace".to_string(), binding.namespace.clone().into());
    record.insert("pod".to_string(), binding.pod.clone().into());
    record.insert("uid".to_string(), binding.uid.clone().into());
    record.insert("data_storage".to_string(), binding.data_storage.clone().into());
    record.insert("domain_id".to_string(), binding.domain_id.into());
    record.insert("container_id".to_string(), binding.container_id.clone().into());
    record.insert("pid".to_string(), binding.pid.into());
    record.insert("mnt_ns_id".to_string(), binding.mnt_ns_id.into());
    let line = serde_json::Value::Object(record).to_string();
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .map_err(|err| format!("failed to open {}: {err}", path.display()))?;
    writeln!(file, "{line}").map_err(|err| format!("failed to append {}: {err}", path.display()))
}

fn write_ready_marker(config: &ScanConfig, mnt_ns_id: u64, domain_id: u32) -> Result<(), String> {
    fs::create_dir_all(&config.ready_dir)
        .map_err(|err| format!("failed to mkdir {}: {err}", config.ready_dir.display()))?;
    let path = config.ready_dir.join(mnt_ns_id.to_string());
    fs::write(&path, format!("{domain_id}\n"))
        .map_err(|err| format!("failed to write {}: {err}", path.display()))
}

fn resolve_bindings_for_pod(pod: &Pod, proc_root: &Path) -> Result<Vec<BindingRecord>, String> {
    let labels = pod.metadata.labels.as_ref().ok_or_else(|| "pod labels missing".to_string())?;
    let data_storage = match labels.get("data-storage") {
        Some(value) => value.clone(),
        None => return Ok(Vec::new()),
    };
    let namespace = pod.metadata.namespace.clone().unwrap_or_default();
    let pod_name = pod.metadata.name.clone().unwrap_or_else(|| "<unknown>".to_string());
    let uid = pod.metadata.uid.clone().unwrap_or_default();
    let statuses = pod.status.container_statuses.as_ref().cloned().unwrap_or_default();
    let mut bindings = Vec::new();
    for status in statuses {
        let Some(raw_container_id) = status.container_id else {
            continue;
        };
        let container_id =
            raw_container_id.split("://").nth(1).map(str::to_string).unwrap_or(raw_container_id);
        let pid = resolve_container_pid(proc_root, &container_id)?;
        let mnt_ns_id = read_mnt_ns_id(proc_root, pid)?;
        bindings.push(BindingRecord {
            namespace: namespace.clone(),
            pod: pod_name.clone(),
            uid: uid.clone(),
            data_storage: data_storage.clone(),
            domain_id: stable_domain_id(&data_storage),
            container_id,
            pid,
            mnt_ns_id,
        });
    }
    Ok(bindings)
}

fn ensure_policy_loaded(
    config: &ScanConfig,
    loaded_policies: &mut std::collections::BTreeSet<(String, u32)>,
    namespace: &str,
    data_storage: &str,
    domain_id: u32,
) -> Result<(), String> {
    if !config.auto_load_policy {
        return Ok(());
    }
    let key = (namespace.to_string(), domain_id);
    if loaded_policies.contains(&key) {
        return Ok(());
    }
    let policy_toml = fetch_policy_bytes(config, namespace, data_storage)?;
    let policy_blob = compile_policy_toml_to_blob(&policy_toml)
        .map_err(|err| format!("failed to compile policy for {namespace}/{data_storage}: {err}"))?;
    let file = File::options()
        .read(true)
        .write(true)
        .open(&config.device_path)
        .map_err(|err| format!("failed to open {}: {err}", config.device_path))?;
    load_policy(&file, domain_id, &policy_blob)
        .map_err(|err| format!("ioctl load-policy failed: {err}"))?;
    loaded_policies.insert(key);
    log(&format!(
        "loaded policy namespace={namespace} data-storage={data_storage} domain_id={domain_id} bytes={} configmap={}{}",
        policy_toml.len(),
        config.policy_configmap_prefix,
        data_storage
    ));
    Ok(())
}

fn parse_scan_config(args: &[String]) -> Result<(ScanConfig, bool), String> {
    let node_name = env::var("NODE_NAME")
        .ok()
        .or_else(|| parse_flag(args, "--node-name").ok())
        .ok_or_else(|| "--node-name or NODE_NAME is required".to_string())?;
    let bindings_file = env::var("DEKO_BINDINGS_FILE")
        .ok()
        .or_else(|| parse_flag(args, "--bindings-file").ok())
        .map(PathBuf::from);
    let proc_root = PathBuf::from(
        env::var("DEKO_HOST_PROC")
            .ok()
            .or_else(|| parse_flag(args, "--proc-root").ok())
            .unwrap_or_else(|| "/host/proc".to_string()),
    );
    let device_path = env::var("DEKO_DEVICE_PATH")
        .ok()
        .or_else(|| parse_flag(args, "--device").ok())
        .unwrap_or_else(|| "/host/dev/deko".to_string());
    let token_path = PathBuf::from(
        env::var("DEKO_TOKEN_PATH").unwrap_or_else(|_| DEFAULT_TOKEN_PATH.to_string()),
    );
    let ca_path =
        PathBuf::from(env::var("DEKO_CA_PATH").unwrap_or_else(|_| DEFAULT_CA_PATH.to_string()));
    let interval_sec = env::var("DEKO_INTERVAL_SEC")
        .ok()
        .or_else(|| parse_flag(args, "--interval-sec").ok())
        .unwrap_or_else(|| "15".to_string())
        .parse::<u64>()
        .map_err(|err| format!("invalid interval: {err}"))?;
    let auto_load_policy =
        env::var("DEKO_AUTO_LOAD_POLICY").unwrap_or_else(|_| "1".to_string()) != "0";
    let policy_configmap_prefix =
        env::var("DEKO_POLICY_CONFIGMAP_PREFIX").unwrap_or_else(|_| "deko-policy-".to_string());
    let policy_configmap_key =
        env::var("DEKO_POLICY_CONFIGMAP_KEY").unwrap_or_else(|_| "policy.toml".to_string());
    let ready_dir = PathBuf::from(
        env::var("DEKO_READY_DIR")
            .ok()
            .or_else(|| parse_flag(args, "--ready-dir").ok())
            .unwrap_or_else(|| "/host/tmp/deko-ready".to_string()),
    );
    let once = has_flag(args, "--once");
    Ok((
        ScanConfig {
            node_name,
            device_path,
            proc_root,
            bindings_file,
            token_path,
            ca_path,
            interval_sec,
            auto_load_policy,
            policy_configmap_prefix,
            policy_configmap_key,
            ready_dir,
        },
        once,
    ))
}

fn run_once(
    config: &ScanConfig,
    seen_bindings: &mut std::collections::BTreeSet<String>,
    loaded_policies: &mut std::collections::BTreeSet<(String, u32)>,
) -> Result<(), String> {
    let pods = fetch_local_node_pods(config)?;
    let mut total_bindings = 0usize;
    let mut new_bindings = 0usize;
    for pod in &pods {
        let pod_name = pod.metadata.name.clone().unwrap_or_else(|| "<unknown>".to_string());
        let bindings = match resolve_bindings_for_pod(pod, &config.proc_root) {
            Ok(bindings) => bindings,
            Err(err) => {
                log(&format!("skip pod {pod_name}: {err}"));
                continue;
            }
        };
        if let Some(first) = bindings.first() {
            if let Err(err) = ensure_policy_loaded(
                config,
                loaded_policies,
                &first.namespace,
                &first.data_storage,
                first.domain_id,
            ) {
                log(&format!("skip pod {pod_name}: failed to load policy: {err}"));
                continue;
            }
        }
        for binding in bindings {
            total_bindings += 1;
            let key = binding_key(&binding);
            if seen_bindings.contains(&key) {
                continue;
            }
            let file = File::options()
                .read(true)
                .write(true)
                .open(&config.device_path)
                .map_err(|err| format!("failed to open {}: {err}", config.device_path))?;
            bind_domain(&file, binding.mnt_ns_id, binding.domain_id)
                .map_err(|err| format!("ioctl bind failed: {err}"))?;
            write_ready_marker(config, binding.mnt_ns_id, binding.domain_id)?;
            if let Some(path) = &config.bindings_file {
                append_binding(path, &binding)?;
            }
            seen_bindings.insert(key);
            new_bindings += 1;
            log(&format!(
                "registered pod={} data-storage={} domain_id={} mnt_ns_id={}",
                binding.pod, binding.data_storage, binding.domain_id, binding.mnt_ns_id
            ));
        }
    }
    log(&format!(
        "completed scan: observed {total_bindings} binding(s), registered {new_bindings} new binding(s)"
    ));
    Ok(())
}

fn scan_command(args: &[String]) -> Result<(), String> {
    let (config, once) = parse_scan_config(args)?;
    let mut seen_bindings = std::collections::BTreeSet::new();
    let mut loaded_policies = std::collections::BTreeSet::new();
    loop {
        run_once(&config, &mut seen_bindings, &mut loaded_policies)?;
        if once {
            return Ok(());
        }
        thread::sleep(Duration::from_secs(config.interval_sec));
    }
}

fn compile_policy_command(args: &[String]) -> Result<(), String> {
    let input = PathBuf::from(parse_flag(args, "--input")?);
    let output = PathBuf::from(parse_flag(args, "--output")?);
    let policy_bytes =
        fs::read(&input).map_err(|err| format!("failed to read {}: {err}", input.display()))?;
    let blob = compile_policy_toml_to_blob(&policy_bytes)
        .map_err(|err| format!("failed to compile {}: {err}", input.display()))?;
    fs::write(&output, &blob)
        .map_err(|err| format!("failed to write {}: {err}", output.display()))?;
    println!(
        "compiled policy input={} output={} bytes={}",
        input.display(),
        output.display(),
        blob.len()
    );
    Ok(())
}

fn load_policy_command(args: &[String]) -> Result<(), String> {
    let device = parse_flag(args, "--device")?;
    let domain_id = parse_u32_flag(args, "--domain-id")?;
    let policy_file = PathBuf::from(parse_flag(args, "--policy-file")?);
    let input_bytes = fs::read(&policy_file)
        .map_err(|err| format!("failed to read {}: {err}", policy_file.display()))?;
    let policy_bytes = if has_flag(args, "--binary") {
        input_bytes
    } else {
        compile_policy_toml_to_blob(&input_bytes)
            .map_err(|err| format!("failed to compile {}: {err}", policy_file.display()))?
    };
    let file = File::options()
        .read(true)
        .write(true)
        .open(&device)
        .map_err(|err| format!("failed to open {device}: {err}"))?;
    load_policy(&file, domain_id, &policy_bytes)
        .map_err(|err| format!("ioctl load-policy failed: {err}"))?;
    println!(
        "loaded policy device={} domain_id={} bytes={} file={}",
        device,
        domain_id,
        policy_bytes.len(),
        policy_file.display()
    );
    Ok(())
}

fn bind_command(args: &[String]) -> Result<(), String> {
    let device = parse_flag(args, "--device")?;
    let mnt_ns_id = parse_u64_flag(args, "--mnt-ns-id")?;
    let domain_id = parse_u32_flag(args, "--domain-id")?;
    let file = File::options()
        .read(true)
        .write(true)
        .open(&device)
        .map_err(|err| format!("failed to open {device}: {err}"))?;
    bind_domain(&file, mnt_ns_id, domain_id).map_err(|err| format!("ioctl bind failed: {err}"))?;
    println!("bound device={} mnt_ns_id={} domain_id={}", device, mnt_ns_id, domain_id);
    Ok(())
}

fn lookup_command(args: &[String]) -> Result<(), String> {
    let device = parse_flag(args, "--device")?;
    let mnt_ns_id = parse_u64_flag(args, "--mnt-ns-id")?;
    let file = File::options()
        .read(true)
        .write(true)
        .open(&device)
        .map_err(|err| format!("failed to open {device}: {err}"))?;
    let result =
        lookup_domain(&file, mnt_ns_id).map_err(|err| format!("ioctl lookup failed: {err}"))?;
    println!(
        "lookup device={} mnt_ns_id={} found={} domain_id={}",
        device, mnt_ns_id, result.found, result.domain_id
    );
    Ok(())
}

fn unbind_command(args: &[String]) -> Result<(), String> {
    let device = parse_flag(args, "--device")?;
    let mnt_ns_id = parse_u64_flag(args, "--mnt-ns-id")?;
    let domain_id = parse_u32_flag(args, "--domain-id")?;
    let file = File::options()
        .read(true)
        .write(true)
        .open(&device)
        .map_err(|err| format!("failed to open {device}: {err}"))?;
    unbind_domain(&file, mnt_ns_id, domain_id)
        .map_err(|err| format!("ioctl unbind failed: {err}"))?;
    println!("unbound device={} mnt_ns_id={} domain_id={}", device, mnt_ns_id, domain_id);
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let result = match args.get(1).map(String::as_str) {
        Some("scan") => scan_command(&args[2..]),
        Some("compile-policy") => compile_policy_command(&args[2..]),
        Some("load-policy") => load_policy_command(&args[2..]),
        Some("bind") => bind_command(&args[2..]),
        Some("lookup") => lookup_command(&args[2..]),
        Some("unbind") => unbind_command(&args[2..]),
        _ => {
            print_usage();
            Err("invalid command".to_string())
        }
    };

    if let Err(err) = result {
        eprintln!("{err}");
        std::process::exit(1);
    }
}
