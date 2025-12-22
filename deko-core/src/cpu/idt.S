
.code64
.section .data
.globl HV_DOORBELL_ADDR
HV_DOORBELL_ADDR:
	.quad 0

.text

idt_handler_ret:
  addq    $8, %rsp

  popq    %r15
  popq    %r14
  popq    %r13
  popq    %r12
  popq    %r11
  popq    %r10
  popq    %r9
  popq    %r8
  popq    %rbp
  popq    %rdi
  popq    %rsi
  popq    %rdx
  popq    %rcx
  popq    %rbx
  popq    %rax

  addq    $8, %rsp
  iretq

.pushsection .entry.text, "ax"

.globl default_return
default_return:
    ud2 // placeholder.

push_regs_no_ghcb:
  pushq   %rbx
  pushq   %rcx
  pushq   %rdx
  pushq   %rsi
  /* Move vector number into RSI */
  movq    0x20(%rsp), %rsi
  /* Save RAX */
  movq    %rax, 0x20(%rsp)
  pushq   %rdi
  pushq   %rbp
  pushq   %r8
  pushq   %r9
  pushq   %r10
  pushq   %r11
  pushq   %r12
  pushq   %r13
  pushq   %r14
  pushq   %r15

  pushq   $0
  movq    %rsp, %rdi
  call    stage2_generic_idt_handler_no_ghcb
  jmp     idt_handler_ret

.popsection
.align 32
.globl stage2_generic_idt_handler_no_ghcb
stage2_generic_idt_handler_no_ghcb:
  i = 0
  .rept 32
  .align 32
  .if ((0x20027d00 >> 1) & 1) == 0
    pushq  $0
  .endif
  pushq $i
  jmp push_regs_no_ghcb
  i = i + 1
  .endr

.pushsection .entry.text, "ax"
push_regs_stage2:
  pushq   %rbx
  pushq   %rcx
  pushq   %rdx
  pushq   %rsi
  /* Move vector number into RSI */
  movq    0x20(%rsp), %rsi
  /* Save RAX */
  movq    %rax, 0x20(%rsp)
  pushq   %rdi
  pushq   %rbp
  pushq   %r8
  pushq   %r9
  pushq   %r10
  pushq   %r11
  pushq   %r12
  pushq   %r13
  pushq   %r14
  pushq   %r15

  pushq   $0 /* ssp */
  movq    %rsp, %rdi
  call    stage2_generic_idt_handler
  jmp     idt_handler_ret

.popsection

.align 32
.globl stage2_generic_idt_handler
stage2_generic_idt_handler:
  i = 0
  .rept 32
  .align 32
  .if ((0x20027d00 >> 1) & 1) == 0
    pushq  $0
  .endif
  pushq $i
  jmp push_regs_stage2
  i = i + 1
  .endr
