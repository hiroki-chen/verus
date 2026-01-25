fn main() {
    println!("cargo:rustc-link-arg-bin=deko-ifc=-nostdlib");
    println!("cargo:rustc-link-arg-bin=deko-ifc=--no-relax");
    println!("cargo:rustc-link-arg-bin=deko-ifc=--build-id=none");
    println!("cargo:rustc-link-arg-bin=deko-ifc=-T./.cargo/policy_engine.ld");
    println!("cargo:rustc-link-arg-bin=deko-ifc=-no-pie");
    println!("cargo:rerun-if-changed=build.rs");
}
