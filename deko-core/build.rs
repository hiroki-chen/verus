use std::process::Command;

use chrono::{DateTime, TimeZone, Utc};

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

    // Set environment variables for the compiled code
    println!("cargo:rustc-env=DEKO_GIT_HASH={}", git_hash);
    println!("cargo:rustc-env=DEKO_BUILD_TIME={}", build_time);

    // Rebuild if git HEAD changes
    println!("cargo:rerun-if-changed=../.git/HEAD");
    println!("cargo:rerun-if-changed=build.rs");
}

fn format_timestamp_from_epoch(epoch: i64) -> String {
    let dt = Utc.timestamp_opt(epoch, 0).single().unwrap_or_else(|| Utc::now());
    dt.format("%Y-%m-%d %H:%M:%S UTC").to_string()
}

fn format_timestamp_now() -> String {
    let dt = Utc::now();
    dt.format("%Y-%m-%d %H:%M:%S UTC").to_string()
}
