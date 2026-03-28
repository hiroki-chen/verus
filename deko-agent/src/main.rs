mod ioctl;
mod policy_compile;

use std::env;
use std::fs::{self, File};
use std::path::PathBuf;

use ioctl::{bind_domain, load_policy, lookup_domain, unbind_domain};
use policy_compile::compile_policy_toml_to_blob;

fn print_usage() {
    eprintln!(
        "usage:
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

fn parse_u32_flag(args: &[String], flag: &str) -> Result<u32, String> {
    parse_flag(args, flag)?.parse::<u32>().map_err(|err| format!("invalid {flag}: {err}"))
}

fn parse_u64_flag(args: &[String], flag: &str) -> Result<u64, String> {
    parse_flag(args, flag)?.parse::<u64>().map_err(|err| format!("invalid {flag}: {err}"))
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
