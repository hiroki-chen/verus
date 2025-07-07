//! Crate for loading the Deko monitor ELF binary.
use core::arch::asm;
use core::fmt::{Debug, Formatter};

use deko_meta::{Header, BOOT_VERSION};
use uefi::boot::{AllocateType, MemoryType};
use uefi::mem::memory_map::MemoryMap;
use uefi::prelude::*;
use uefi::proto::media::file::{File, FileInfo, FileMode, FileType};
use uefi::proto::media::fs::SimpleFileSystem;
use uefi::table::cfg::ACPI2_GUID;
use uefi::{println, CStr16, Result};
use uefi_raw::protocol::file_system::FileAttribute;
use uefi_raw::table::configuration::ConfigurationTable;
use uefi_raw::table::system::SystemTable;
use xmas_elf::header::Type;
use xmas_elf::program::{self, SegmentData};
use xmas_elf::ElfFile;

pub struct DekoKernel<'deko> {
    pub elf: ElfFile<'deko>,
    pub size: usize,
    /// The start address of the kernel in memory.
    pub start_address: *const u8,
}

impl<'deko> DekoKernel<'deko> {
    /// Creates a new `DekoKernel` from the given ELF file.
    pub fn new(raw_bytes: &'deko [u8]) -> Self {
        let elf = ElfFile::new(raw_bytes).expect("Failed to parse ELF file");

        // Do a sanity check on the ELF.
        let ty = elf.header.pt2.type_().as_type();
        if ty != Type::Executable && ty != Type::SharedObject {
            panic!("Invalid ELF type: expected `Executable` or `SharedObject`, found {:?}", ty);
        }

        println!("[+] Kernel header: {:#x?}", elf.header.pt2);

        Self { elf, size: raw_bytes.len(), start_address: raw_bytes.as_ptr() }
    }

    /// Unpack and load the kernel image into the memory
    fn load(&self) -> Result<()> {
        let paddr_base = self.start_address as u64;

        for segment in self.elf.program_iter() {
            if segment.get_type().expect("Failed to get segment type") == program::Type::Load {
                // Skip non-loadable segments.
                let mem_size = segment.mem_size();
                let file_size = segment.file_size();
                let paddr = segment.physical_addr();
                let vaddr = segment.virtual_addr();

                assert_eq!(paddr, vaddr, "Kernel segments must be identity-mapped for booting");

                println!(
                    "[+] Segment: type={:?}, paddr={:#x}, vaddr={:#x}, mem_size={:#x}, file_size={:#x}",
                    segment.get_type().expect("Failed to get segment type"),
                    paddr,
                    vaddr,
                    mem_size,
                    file_size
                );

                let page_count = ((mem_size - 1) / 0x1000) + 1;
                boot::allocate_pages(
                    AllocateType::Address(paddr),
                    MemoryType::LOADER_CODE,
                    page_count as usize,
                )
                .expect("Failed to allocate memory for kernel segment");

                // --- Step 2b: Copy the segment data from the file buffer ---
                // xmas-elf gives us the content of the segment directly from the file buffer.
                let segment_data_in_file = if let SegmentData::Undefined(d) =
                    segment.get_data(&self.elf).expect("Failed to get segment data from ELF file")
                {
                    d
                } else {
                    panic!("Unexpected segment data type");
                };

                // The destination is the physical address we just allocated.
                let dest_slice =
                    unsafe { core::slice::from_raw_parts_mut(paddr as *mut u8, mem_size as usize) };

                // Copy the part of the segment that exists in the file
                dest_slice[..file_size as usize].copy_from_slice(segment_data_in_file);

                // --- Step 2c: Zero out the .BSS section ---
                // If mem_size > file_size, the remaining space is the .bss section
                // and must be zeroed.
                if mem_size > file_size {
                    let bss_start_offset = file_size as usize;
                    dest_slice[bss_start_offset..].fill(0);
                }
            }
        }

        Ok(())
    }

    pub unsafe fn enter(&self) -> ! {
        self.load().expect("Failed to load Deko kernel");

        // In the context of UEFI (Unified Extensible Firmware Interface),
        // the memory_map_size parameter specifies the size of the memory
        // map that is provided by the UEFI firmware. The memory map is a
        // table that contains information about the memory regions that
        // are available to the operating system, such as the size and type
        // of each region. This information is important for the operating
        // system to properly allocate and manage memory resources.
        let mmap = boot::exit_boot_services(None); // use defaul LOADER_DATA.
        let mmap_size = mmap.len();

        // Here we construct a header for the deko monitor.
        let mut header = Header::default();
        header.version = BOOT_VERSION;
        header.mmap = mmap.buffer().as_ptr() as _;
        header.mmap_len = mmap_size as u64;
        header.kernel_entry = self.start_address as u64;

        // Note we do page table construction and virtual memory allocation
        // inside the deko monitor itself so at this timepoint the addresses
        // are all real physical addresses and no page tables enabled.
        asm!(
            // "mov rsp, 0xdeadbeef",
            "jmp {}",
            "ud2",
            in(reg)  self.elf.header.pt2.entry_point(),
            // We also have an implicit argument here.
            in("rdi") &header as *const Header as u64,
            options(noreturn),
        );
    }
}

impl<'deko> Debug for DekoKernel<'deko> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DekoKernel")
            .field("size", &self.size)
            .field("start_address", &self.start_address)
            .finish()
    }
}

const KERNEL: &str = "deko.bin";

pub unsafe fn kernel_init(st: &SystemTable) -> Result<DekoKernel<'static>> {
    let acpi = find_acpi_table(st)?;
    println!("[OK] ACPI 2.0 table found at: {:?}", acpi.vendor_table);

    let kernel_data = load_file(KERNEL).expect("Failed to load Deko kernel file");
    println!("[OK] Loaded '{}' ({} bytes) into memory", KERNEL, kernel_data.len());

    let kernel = DekoKernel::new(kernel_data);
    println!("[OK] Deko kernel initialized: {:?}", kernel);

    Ok(kernel)
}

unsafe fn find_acpi_table(st: &SystemTable) -> Result<&'static ConfigurationTable> {
    let configuration_table_len = st.number_of_configuration_table_entries;
    let configuration_table =
        core::slice::from_raw_parts(st.configuration_table, configuration_table_len);

    let acpi = configuration_table
        .iter()
        .find(|entry| entry.vendor_guid == ACPI2_GUID)
        .expect("ACPI 2.0 table not found");

    Ok(acpi)
}

fn load_file(filename: &str) -> Result<&'static [u8]> {
    let handle = boot::get_handle_for_protocol::<SimpleFileSystem>()
        .expect("Failed to get handle for SimpleFileSystem protocol");
    let mut fs = boot::open_protocol_exclusive::<SimpleFileSystem>(handle)
        .expect("Failed to open SimpleFileSystem protocol");

    let mut root = fs.open_volume().expect("Failed to open file system volume");

    let mut buf = [0u16; 0x40];
    let cstr_filename = CStr16::from_str_with_buf(filename, &mut buf)
        .expect("Failed to create CStr16 from filename");

    let file_handle = root
        .open(cstr_filename, FileMode::Read, FileAttribute::empty())
        .expect("Failed to open file");

    let mut file = match file_handle.into_type().unwrap() {
        FileType::Regular(f) => f,
        _ => panic!("Expected a regular file"),
    };

    let mut file_info = [0u8; 2048];
    let info = file.get_info::<FileInfo>(&mut file_info).unwrap();
    let file_size = info.file_size() as usize;

    // Allocate memory for the file content
    let mem_ptr = boot::allocate_pages(
        AllocateType::AnyPages,
        MemoryType::LOADER_DATA,
        ((file_size - 1) / 0x1000usize) + 1,
    )
    .expect("Failed to allocate enough memory for the file")
    .as_ptr();

    // Read the file into the allocated memory
    let mem_slice = unsafe { core::slice::from_raw_parts_mut(mem_ptr, file_size) };
    let bytes_read = file.read(mem_slice).expect("Cannot read file into memory!");

    Ok(&mem_slice[..bytes_read])
}

/// This function exists only under debug builds for debugging purposed.
///
/// We also allow `dead_code` for code analysis.
#[cfg(debug_assertions)]
#[allow(dead_code)]
fn list_directory(dir: &mut uefi::proto::media::file::Directory) {
    let mut buffer = [0u8; 256];
    uefi::println!("\n--- Listing Directory Contents ---");
    // Rewind to make sure we start from the beginning
    // dir.rewind().expect("Failed to rewind directory");
    loop {
        match dir.read_entry(&mut buffer) {
            Ok(Some(file_info)) => {
                // file_info is a &FileInfo
                uefi::println!("  -> Found: '{}'", file_info.file_name());
            }
            Ok(None) => {
                // No more entries
                break;
            }
            Err(e) => {
                uefi::println!("[ERROR] Could not read directory entry: {:?}", e);
                break;
            }
        }
    }

    uefi::println!("--- End of Directory Listing ---");
}
