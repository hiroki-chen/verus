fn main() {
    // Linker arguments
    println!("cargo:rustc-link-arg-bin=stage2=-nostdlib");
    // println!("cargo:rustc-link-arg-bin=stage2=--build-id=none");
    println!("cargo:rustc-link-arg-bin=stage2=-T./.cargo/stage2.ld");
    println!("cargo:rustc-link-arg-bin=stage2=-no-pie");

    // Rebuild if git HEAD changes
    println!("cargo:rerun-if-changed=../.git/HEAD");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../.cargo/stage2.ld");
}
