use std::process::Command;

use chrono::{TimeZone, Utc};

fn main() {
    // Capture git commit hash
    let git_hash = Command::new("git")
        .args(&["rev-parse", "--short=8", "HEAD"])
        .output()
        .ok()
        .and_then(|output| {
            if output.status.success() {
                String::from_utf8(output.stdout).ok()
            } else {
                None
            }
        })
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    // Capture build timestamp
    let build_time = std::env::var("SOURCE_DATE_EPOCH")
        .ok()
        .and_then(|epoch| epoch.parse::<i64>().ok())
        .map(|epoch| format_timestamp_from_epoch(epoch))
        .unwrap_or_else(|| format_timestamp_now());

    // Capture log level from environment variable
    let log_level =
        std::env::var("DEKO_LOG_LEVEL").unwrap_or_else(|_| "INFO".to_string()).to_uppercase();

    // Validate log level and set appropriate compile-time flags
    let log_level_num = match log_level.as_str() {
        "ERROR" => 1,
        "WARN" | "WARNING" => 2,
        "INFO" => 3,
        "DEBUG" => 4,
        "TRACE" => 5,
        _ => {
            eprintln!("Warning: Invalid DEKO_LOG_LEVEL '{}'. Using INFO level.", log_level);
            3
        }
    };

    // Set environment variables for the compiled code
    println!("cargo::rustc-check-cfg=cfg(log_level_info)");
    println!("cargo::rustc-check-cfg=cfg(log_level_warn)");
    println!("cargo::rustc-check-cfg=cfg(log_level_error)");
    println!("cargo::rustc-check-cfg=cfg(log_level_debug)");
    println!("cargo::rustc-check-cfg=cfg(log_level_trace)");

    println!("cargo:rustc-env=DEKO_GIT_HASH={}", git_hash);
    println!("cargo:rustc-env=DEKO_BUILD_TIME={}", build_time);
    println!("cargo:rustc-env=DEKO_LOG_LEVEL={}", log_level);
    println!("cargo:rustc-env=DEKO_LOG_LEVEL_NUM={}", log_level_num);

    // Set conditional compilation flags based on log level
    if log_level_num >= 1 {
        println!("cargo:rustc-cfg=log_level_error");
    }
    if log_level_num >= 2 {
        println!("cargo:rustc-cfg=log_level_warn");
    }
    if log_level_num >= 3 {
        println!("cargo:rustc-cfg=log_level_info");
    }
    if log_level_num >= 4 {
        println!("cargo:rustc-cfg=log_level_debug");
    }
    if log_level_num >= 5 {
        println!("cargo:rustc-cfg=log_level_trace");
    }

    // Rebuild if environment variables change
    println!("cargo:rerun-if-env-changed=DEKO_LOG_LEVEL");

    // Rebuild if git HEAD changes
    println!("cargo:rerun-if-changed=../.git/HEAD");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/cpu/switch.S");
    println!("cargo:rerun-if-changed=src/cpu/idt.S");
}

fn format_timestamp_from_epoch(epoch: i64) -> String {
    let dt = Utc.timestamp_opt(epoch, 0).single().unwrap_or_else(|| Utc::now());
    dt.format("%Y-%m-%d %H:%M:%S UTC").to_string()
}

fn format_timestamp_now() -> String {
    let dt = Utc::now();
    dt.format("%Y-%m-%d %H:%M:%S UTC").to_string()
}
