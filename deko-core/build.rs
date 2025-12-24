use std::process::Command;

use chrono::{TimeZone, Utc};

/// A stub representation of an IDT entry for generating assembly handlers.
struct EntryStub {
    name: &'static str,
    handler: &'static str,
    errno: bool,
    vec: u32,
}

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

    gen_idt_handler();
}

fn format_timestamp_from_epoch(epoch: i64) -> String {
    let dt = Utc.timestamp_opt(epoch, 0).single().unwrap_or_else(|| Utc::now());
    dt.format("%Y-%m-%d %H:%M:%S UTC").to_string()
}

fn format_timestamp_now() -> String {
    let dt = Utc::now();
    dt.format("%Y-%m-%d %H:%M:%S UTC").to_string()
}

fn generate_irq(stub: &EntryStub) -> String {
    format!(
        r#"
        .globl {name}_handler
    {name}_handler:
        pushq	$0
        push_regs
        movl	${vector}, %esi
        movq	%rsp, %rdi
        xorl	%edx, %edx
        call	ex_handler_{handler}
        jmp	default_return
    "#,
        name = stub.name,
        handler = stub.handler,
        vector = stub.vec,
    )
}

fn generate_entry(stub: &EntryStub) -> String {
    format!(
        r#"
        .globl {name}_handler
    {name}_handler:
        clac

    {push_error}
        push_regs
        testl	${if_flag}, {excep_flags_off}(%rsp)
        jz	.Lskip_{name}
        sti
    .Lskip_{name}:
        movl	${vector}, %esi
        movq	%rsp, %rdi
        xorl	%edx, %edx
        call	ex_handler_{handler}
        jmp	default_return
    "#,
        name = stub.name,
        handler = stub.handler,
        vector = stub.vec,
        push_error = if !stub.errno { "\tpushq\t$0" } else { "" },
        if_flag = "0x200", // Example
        excep_flags_off = "0x98",
    )
}

/// Generate IDT handler functions in assemblies for each gates.
fn gen_idt_handler() {
    let entries = vec![
        EntryStub { name: "de", handler: "panic", errno: false, vec: 0 },
        EntryStub { name: "db", handler: "panic", errno: false, vec: 1 }, // debug not used
        EntryStub { name: "nmi", handler: "panic", errno: false, vec: 2 },
        EntryStub { name: "bp", handler: "panic", errno: false, vec: 3 },
        EntryStub { name: "of", handler: "panic", errno: false, vec: 4 },
        EntryStub { name: "br", handler: "panic", errno: false, vec: 5 },
        EntryStub { name: "ud", handler: "panic", errno: false, vec: 6 },
        EntryStub { name: "nm", handler: "panic", errno: false, vec: 7 },
        EntryStub { name: "df", handler: "double_fault", errno: true, vec: 8 },
        EntryStub { name: "ts", handler: "panic", errno: true, vec: 10 },
        EntryStub { name: "np", handler: "panic", errno: true, vec: 11 },
        EntryStub { name: "ss", handler: "panic", errno: true, vec: 12 },
        EntryStub { name: "gp", handler: "general_protection", errno: true, vec: 13 },
        EntryStub { name: "pf_early", handler: "page_fault_early", errno: true, vec: 14 },
        EntryStub { name: "pf", handler: "page_fault", errno: true, vec: 14 },
        EntryStub { name: "mf", handler: "panic", errno: false, vec: 16 },
        EntryStub { name: "ac", handler: "panic", errno: true, vec: 17 },
        EntryStub { name: "mce", handler: "panic", errno: false, vec: 18 },
        EntryStub { name: "xm", handler: "panic", errno: false, vec: 19 },
        EntryStub { name: "ve", handler: "ve", errno: false, vec: 20 },
        EntryStub { name: "cp", handler: "panic", errno: true, vec: 21 },
        EntryStub { name: "vc", handler: "vmm_handler", errno: true, vec: 29 },
        EntryStub { name: "sx", handler: "panic", errno: true, vec: 30 },
        EntryStub { name: "int80", handler: "syscall_handler", errno: false, vec: 0x80 },
        // Add more entries as needed...
    ];

    // Then write this to the file and then we can link agains it.
    let mut assembly_code = String::new();
    for entry in &entries {
        assembly_code.push_str(&generate_entry(entry));
    }

    assembly_code.push_str(&generate_irq(&EntryStub {
        name: "irq_ipi",
        handler: "irq_ipi",
        errno: false,
        vec: 0xe0,
    }));
    assembly_code.push_str(&generate_irq(&EntryStub {
        name: "irq_int_inj",
        handler: "irq_int_inj",
        errno: false,
        vec: 0x50,
    }));

    let final_code = format!(
        r#"
    // Auto-generated by build.rs - do not edit.
    .code64
    .pushsection .entry.text, "ax"
    .macro push_regs
        pushq	%rax
        pushq	%rbx
        pushq	%rcx
        pushq	%rdx
        pushq	%rsi
        pushq	%rdi
        pushq	%rbp
        pushq	%r8
        pushq	%r9
        pushq	%r10
        pushq	%r11
        pushq	%r12
        pushq	%r13
        pushq	%r14
        pushq	%r15
    .endm

    {body}
    .popsection
    "#,
        body = assembly_code
    );

    std::fs::write("src/cpu/idt_gen.S", final_code).expect("Unable to write IDT assembly file");
}
