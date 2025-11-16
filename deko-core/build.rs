use std::process::Command;

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
        .map(|epoch| {
            use std::time::UNIX_EPOCH;
            let dt = UNIX_EPOCH + std::time::Duration::from_secs(epoch as u64);
            format_timestamp(dt)
        })
        .unwrap_or_else(|| format_timestamp(std::time::SystemTime::now()));

    // Set environment variables for the compiled code
    println!("cargo:rustc-env=DEKO_GIT_HASH={}", git_hash);
    println!("cargo:rustc-env=DEKO_BUILD_TIME={}", build_time);

    // Rebuild if git HEAD changes
    println!("cargo:rerun-if-changed=../.git/HEAD");
    println!("cargo:rerun-if-changed=build.rs");
}

fn format_timestamp(time: std::time::SystemTime) -> String {
    use std::time::{Duration, UNIX_EPOCH};

    let duration = time.duration_since(UNIX_EPOCH).unwrap_or(Duration::from_secs(0));
    let seconds = duration.as_secs();

    // Simple UTC timestamp formatting (YYYY-MM-DD HH:MM:SS UTC)
    let days_since_epoch = seconds / 86400;
    let seconds_today = seconds % 86400;

    // Days since Unix epoch (1970-01-01) to approximate date
    // This is a simplified calculation
    let years_since_1970 = days_since_epoch / 365;
    let year = 1970 + years_since_1970;

    let hour = seconds_today / 3600;
    let minute = (seconds_today % 3600) / 60;
    let second = seconds_today % 60;

    // Simplified date calculation (not accounting for leap years precisely)
    let day_of_year = days_since_epoch % 365;
    let month = (day_of_year / 30) + 1; // Rough approximation
    let day = (day_of_year % 30) + 1;

    format!(
        "{:04}-{:02}-{:02} {:02}:{:02}:{:02} UTC",
        year,
        month.min(12),
        day.min(31),
        hour,
        minute,
        second
    )
}
