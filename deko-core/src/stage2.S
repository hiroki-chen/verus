.text
.section ".startup.text","ax"
.code32

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

  ljmpl $0x8, $.Lsnp_cs

.Lsnp_cs:
  movl $pgtable_end, %ecx
  subl $pgtable, %ecx
  shrl $2, %ecx
  xorl %eax, %eax
  movl $pgtable, %edi
  rep stosl

  call get_pte_c_bit
  movl %eax, %edx

  movl $pgtable, %edi
  leal 0x1007(%edi), %eax
  movl %eax, 0(%edi)
  addl %edx, 4(%edi)

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

  addl $0x1000, %edi
  movl $0x00000183, %eax
  movl $2048, %ecx
  1: movl %eax, 0(%edi)
  addl %edx, 4(%edi)
  addl $0x00200000, %eax
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
    *
    * - Pass &Stage2LaunchInfo as the first argument (%rdi)
    * - Make sure (%rsp + 8) is 16b-aligned when control is transferred
    *   to deko_main
    */
  movl %ebp, %edi
  andq $~0xf, %rsp
  call deko_main

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

.globl bsp_stack
bsp_stack:
.globl bsp_stack_end
bsp_stack_end:
