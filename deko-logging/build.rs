fn main() {
    for cfg in [
        "log_level_error",
        "log_level_warn",
        "log_level_info",
        "log_level_debug",
        "log_level_trace",
    ] {
        println!("cargo:rustc-check-cfg=cfg({cfg})");
    }

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

    // Rebuild if this build script changes
    println!("cargo:rerun-if-changed=build.rs");
}
