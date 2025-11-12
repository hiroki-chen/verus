.text
.section ".startup.text","ax"
.code32

// Constants for memory layout.
.equ STAGE2_START,    0x808000      // 8 +32(KiB) MB - Stage2 base address
.equ STAGE2_MAXLEN,   0xC8000       // ~832 KB - Maximum Stage2 length
.equ LOWMEM_START,    0x0           // Low memory start
.equ LOWMEM_END,      0xA0000       // 640 KB - End of low memory
.equ SHARED_BIT,      0x1          // Shared memory bit

.org 0
.globl startup_32

startup_32:
  movl %esp, %ebp

  movl $gdt64_desc, %eax
  lgdt (%eax)

  movw $0x10, %ax
  movw %ax, %ds
  movw %ax, %es
  movw %ax, %fs
  movw %ax, %gs
  movw %ax, %ss

  ljmpl $0x8, $.LSNP_setup

// This pieceo of code sets up the initial page table for our 64bit DEKO monitor.
// This page table identity-maps the physical addresses.
.LSNP_setup:
  // Clear out the page table.
  movl $pgtable_end, %ecx
  subl $pgtable, %ecx
  shrl $2, %ecx
  xorl %eax, %eax
  movl $pgtable, %edi
  rep stosl

  call get_pte_c_bit
  // The return value should be 0x80000 to be stored in 32bit registers.
  movl %eax, %edx

  // Begin to fill the page table.
  movl $pgtable, %edi
  // eax = &pgtable + 0x1000 + flags(7)
  // level3 -> level2
  leal 0x1007(%edi), %eax
  movl %eax, 0(%edi)
  addl %edx, 4(%edi)

  // level 2-> level 1 only four entries needed for now.
  addl $0x1000, %edi
  leal 0x1007(%edi), %eax
  movl $4, %ecx
  1: movl %eax, 0(%edi)
  addl %edx, 4(%edi)
  addl $0x1000, %eax
  addl $8, %edi
  decl %ecx
  jnz 1b
  andl $0xfffff000, %edi

  // level 1 -> level 0 is based on 2MB pages. note %eax.
  addl $0x1000, %edi
  movl $0x00000183, %eax  // 0x183 => 0001 1000 0011    GLOBAL / HUGE / W / P
  movl $2048, %ecx
  1: movl %eax, 0(%edi)
  addl %edx, 4(%edi)
  addl $0x00200000, %eax // 2MB offset!!!
  addl $8, %edi
  decl %ecx
  jnz 1b

  /* Insert a self-map entry */
  movl $pgtable, %edi
  movl %edi, %eax
  orl $0x63, %eax
  movl %eax, 8*493(%edi)
  movl $0x80000000, %eax
  orl %edx, %eax
  movl %eax, 0xF6C(%edi)

  jmp 2f

2:
  /* Enable 64bit PTEs, CR4.PAE. */
  movl %cr4, %eax
  bts $5, %eax
  movl %eax, %cr4

  /* Enable long mode, EFER.LME. Also ensure NXE is set. */
  movl $0xC0000080, %ecx
  rdmsr
  movl %eax, %ebx
  orl $0x900, %eax
  cmp %eax, %ebx
  jz 3f
  wrmsr
3:
  /* Load the static page table root. */
  movl $pgtable, %eax
  movl %eax, %cr3

  /* Enable paging, CR0.PG. */
  movl %cr0, %eax
  bts $31, %eax
  movl %eax, %cr0

  ljmpl $0x18, $startup_64

get_pte_c_bit:
  /*
  * Check if this is an SNP platform.  If not, there is no C bit.
  */
  cmpl $1, 8(%ebp)
  jnz .Lno_sev_snp

  /*
  * Check that the SNP_Active bit in the SEV_STATUS MSR is set.
  */
  movl $0xC0010131, %ecx
  rdmsr

  testl $0x04, %eax
  jz .Lno_sev_snp

  /*
  * Check whether VTOM is selected
  */
  testl $0x08, %eax
  jnz .Lvtom

  /* Determine the PTE C-bit position from the CPUID page. */

  /* Locate the table.  The pointer to the CPUID page is 12 bytes into
  * the stage2 startup structure. */
  movl 12(%ebp), %ecx
  /* Read the number of entries. */
  movl (%ecx), %eax
  /* Create a pointer to the first entry. */
  leal 16(%ecx), %ecx

.Lcheck_entry:
  /* Check that there is another entry. */
  test %eax, %eax
  je .Lno_sev_snp

  /* Check the input parameters of the current entry. */
  cmpl $0x8000001f, (%ecx) /* EAX_IN */
  jne .Lwrong_entry
  cmpl $0, 4(%ecx) /* ECX_IN */
  jne .Lwrong_entry
  cmpl $0, 8(%ecx) /* XCR0_IN (lower half) */
  jne .Lwrong_entry
  cmpl $0, 12(%ecx) /* XCR0_IN (upper half) */
  jne .Lwrong_entry
  cmpl $0, 16(%ecx) /* XSS_IN (lower half) */
  jne .Lwrong_entry
  cmpl $0, 20(%ecx) /* XSS_IN (upper half) */
  jne .Lwrong_entry

  /* All parameters were correct. */
  jmp .Lfound_entry

.Lwrong_entry:
  /*
    * The current entry doesn't contain the correct input
    * parameters. Try the next one.
    */
  decl %eax
  addl $0x30, %ecx
  jmp .Lcheck_entry

.Lfound_entry:
  /* Extract the c-bit location from the cpuid entry. */
  movl 28(%ecx), %ebx
  andl $0x3f, %ebx

  /*
    * Verify that the C-bit position is within reasonable bounds:
    * >= 32 and < 64.
    */
  cmpl $32, %ebx
  jl .Lno_sev_snp
  cmpl $64, %ebx
  jae .Lno_sev_snp

  subl $32, %ebx
  xorl %eax, %eax
  btsl %ebx, %eax
  ret

.Lvtom:
  xorl %eax, %eax
  ret

.Lno_sev_snp:
  // Die
  ud2

.code64
startup_64:
  /* Reload the data segments with 64bit descriptors. */
  movw $0x20, %ax
  movw %ax, %ds
  movw %ax, %es
  movw %ax, %fs
  movw %ax, %gs
  movw %ax, %ss

  test %esi, %esi
  jz .Lbsp_main

.Lbsp_main:
  /* Clear out .bss and transfer control to the main stage2 code. */
  xorq %rax, %rax
  leaq _bss(%rip), %rdi
  leaq _ebss(%rip), %rcx
  subq %rdi, %rcx
  shrq $3, %rcx
  rep stosq

  /*
    * Follow the C calling convention for x86-64:
    * - Wrap information as a `Ctx` struct and pass its pointer as the first argument (%rdi)
    *   -  Store the Stage2Launchinfo pointer in ctx->stage2_info (offset 0)
    *   -  Store the page table base address in ctx->pgtable (offset 8)
    *   -  Store the gdt pointer in ctx->gdt (offset 16)
    *   -  Store the mapping space in ctx->mapping_space (offset 24)
    * - Pass control to deko_main
    * - Make sure (%rsp + 8) is 16b-aligned when control is transferred
    *   to deko_main
    *
    * DekoCtx structure layout:
    * struct DekoCtx
    *     stage2_launch_info: DekoPPtr<Stage2LaunchInfo>,  // offset 0
    *     pgtable: DekoPPtr<PageTable>,                    // offset 8  
    *     gdt: DekoPPtr<GlobalDescriptorTable>,            // offset 16
    *     mapping_space: MappingSpace,                     // offset 24
    *     private_bit: u64,                                // offset 72
    *     shared_bit: u64,                                 // offset 80
    *
    *
    * MappingSpace structure layout:
    * struct MappingSpace
    *     kernel: FixedAddressMappingRange,                // offset 24
    *     physmap: FixedAddressMappingRange,               // offset 48
    *
    *
    * FixedAddressMappingRange structure layout:
    * struct FixedAddressMappingRange 
    *     virt_start: VirtAddr,                            // 8 bytes
    *     virt_end: VirtAddr,                              // 8 bytes  
    *     phys_start: PhysAddr,                            // 8 bytes
    * 
    */
  movq $deko_bsp_ctx, %rdi

  // Store Stage2LaunchInfo pointer (offset 0)
  movl %ebp, (%rdi)

  // Get the stage2_end information.
  xorl %eax, %eax
  movl 20(%ebp), %eax
  
  // Store page table address (offset 8)
  movq $pgtable, 8(%rdi)
  
  // Store GDT descriptor address (offset 16)
  movq $gdt64_desc, 16(%rdi)
  
  // Populate MappingSpace at offset 24
  // kernel: FixedAddressMappingRange (offset 24)
  movq $STAGE2_START, 24(%rdi)              // kernel.virt_start = STAGE2_START
  movq %rax, 32(%rdi)                       // kernel.virt_end 
  movq $STAGE2_START, 40(%rdi)              // kernel.phys_start = STAGE2_START (identity mapped)
  
  // physmap: FixedAddressMappingRange (offset 48)
  movq $LOWMEM_START, 48(%rdi)              // physmap.virt_start = LOWMEM_START
  movq $LOWMEM_END, 56(%rdi)                // physmap.virt_end = LOWMEM_END
  movq $LOWMEM_START, 64(%rdi)              // physmap.phys_start = LOWMEM_START (identity mapped)

  // bits.
  // FIXME: The weird thing is that rdx value is incorrect.
  movabsq $0x8000000000000, %rdx  // Load the calculated private_bit into %rax
  movq %rdx, 72(%rdi)      // Store the calculated private_bit
  movq $SHARED_BIT, 80(%rdi)           // Store the shared_bit

  andq $~0xf, %rsp
  call deko_main

.Lfail:
  ud2

.data
.align 4

idt32:
  .rept 32
  .quad 0
  .endr
idt32_end:

idt32_desc:
  .word idt32_end - idt32 - 1
  .long idt32

idt64:
  .rept 32
  .octa 0
  .endr
idt64_end:

idt64_desc:
  .word idt64_end - idt64 - 1
  .quad idt64

  .align 256
gdt64:
  .quad 0
  .quad 0x00cf9a000000ffff /* 32 bit code segment */
  .quad 0x00cf93000000ffff /* 32 bit data segment */
  .quad 0x00af9a000000ffff /* 64 bit code segment */
  .quad 0x00cf92000000ffff /* 64 bit data segment */
gdt64_end:

gdt64_desc:
  .word gdt64_end - gdt64 - 1
  .quad gdt64

.align 0x1000
.globl pgtable
pgtable:
.fill 0x7000, 1, 0
pgtable_end:

.align 8
deko_bsp_ctx:
  .fill 0x50, 1, 0
  /* Pre-populate the mapping space? */
deko_bsp_ctx_end:

.globl bsp_stack
bsp_stack:
.globl bsp_stack_end
bsp_stack_end:
