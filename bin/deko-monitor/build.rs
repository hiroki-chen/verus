fn main() {
    println!("cargo:rustc-link-arg-bin=deko=-nostdlib");
    println!("cargo:rustc-link-arg-bin=deko=--no-relax");
    println!("cargo:rustc-link-arg-bin=deko=--build-id=none");
    println!("cargo:rustc-link-arg-bin=deko=-T./.cargo/deko.ld");
    println!("cargo:rustc-link-arg-bin=deko=-no-pie");

    // Rebuild if git HEAD changes
    println!("cargo:rerun-if-changed=../.git/HEAD");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../.cargo/stage2.ld");
}
