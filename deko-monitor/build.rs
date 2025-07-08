fn main() {
    println!("cargo:rerun-if-changed=../.cargo/monitor.ld");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-link-arg=-no-pie");
    println!("cargo:rustc-link-arg=-nostdlib");
    println!("cargo:rustc-link-arg=--build-id=none");
}
