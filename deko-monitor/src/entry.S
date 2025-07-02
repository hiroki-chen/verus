.globl boot_stack
.globl boot_stack_end
.globl stack_guard_page
.globl sm_entry
.globl sm_end
.globl ap_start

.globl _start

_start:
sm_entry:
    /*
     * The hypervisor places the initial VMSA for VMPL0 at a fixed address relative to the
     * SVSM base. The VMSA contains guest state, including the initial stack pointer for
     * VMPL0. Often, the VMSA is at a known offset from the SVSM base.
     *
     * The VMSA's `sev_features` field should be checked to ensure SNP is active.
     */
    cld
    cli
    movq %rsi, %rdi
    call bsp_entry

    movq stack_guard_page(%rip), %rax
    movq $0, %rcx
    movq $0, %rdx
    .byte 0XF2, 0X0F, 0X01, 0XFF 
    leaq boot_stack_end(%rip), %rsp
    callq bsp_entry

.align 4096

ap_start:
    cld
    cli
    callq ap_entry
ap_loop:
    hlt
    jmp ap_loop

.section .data
.align 4096

stack_guard_page:
    .space 4096
boot_stack:
    .space 4096
    .space 4096
    .space 4096
    .space 4096
    .space 4096
    .space 4096
    .space 4096
    .space 4096
    .space 4096
    .space 4096

boot_stack_end:
    ud2

.section .bss
.align 8
sm_end:
