fn main() {
    let elf_data =
        std::fs::read("target/x86_64-snp-deko/debug/deko.elf").expect("Failed to read ELF file");

    let elf = elf::Elf64File::read(&elf_data).unwrap();
}
