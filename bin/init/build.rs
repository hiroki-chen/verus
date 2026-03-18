use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let linker_script = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap())
        .join("..")
        .join("..")
        .join(".cargo")
        .join("user.ld");

    println!("cargo:rustc-link-arg=-no-pie");
    println!("cargo:rustc-link-arg=-T{}", linker_script.display());
}
