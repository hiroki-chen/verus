fn main() {
    println!("cargo:rerun-if-changed=../.cargo/monitor.ld");
    println!("cargo:rerun-if-changed=build.rs");
}
