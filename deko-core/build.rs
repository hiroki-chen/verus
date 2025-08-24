fn main() {
    println!("cargo:rustc-link-arg-bin=stage2=-nostdlib");
    println!("cargo:rustc-link-arg-bin=stage2=--build-id=none");
    println!("cargo:rustc-link-arg-bin=stage2=-T./.cargo/stage2.ld");
    println!("cargo:rustc-link-arg-bin=stage2=-no-pie");

    println!("cargo:rustc-link-arg-bin=deko=-nostdlib");
    println!("cargo:rustc-link-arg-bin=deko=--no-relax");
    println!("cargo:rustc-link-arg-bin=deko=--build-id=none");
    println!("cargo:rustc-link-arg-bin=deko=-T./.cargo/deko.ld");
    println!("cargo:rustc-link-arg-bin=deko=-no-pie");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../.cargo/stage2.ld");
    println!("cargo:rerun-if-changed=../.cargo/deko.ld");
}
