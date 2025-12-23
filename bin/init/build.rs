fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    println!("cargo:rustc-link-arg=-no-pie");
    println!("cargo:rustc-link-arg=-T./.cargo/user.ld");
}
