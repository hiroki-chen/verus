.globl boot_stack
.globl boot_stack_end
.globl stack_guard_page
.globl sm_entry
.globl sm_end
.globl ap_entry

.globl _start

_start:
sm_entry:
    cld
    cli
    mov %rsi, %rdi
    call bsp_entry
    
    mov stack_guard_page(%rsi), $rax
    mov $0, %rcx
    mov $0, %rdx
    .byte 0XF2, 0X0F, 0X01, 0XFF 
    lea boot_stack_end(%rsi), %rsp
    call bsp_entry
    
.align 4096

ap_entry:
    cld
    cli
    call ap_entry
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
    ud2
    hlt
