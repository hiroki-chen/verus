fn main() {
    let elf_path = "target/x86_64-snp-deko/debug/deko.elf";

    let elf_data = std::fs::read(elf_path).expect("Failed to read ELF file");
    let elf_file = elf::Elf64File::read(&elf_data).expect("Failed to parse ELF file");
}
