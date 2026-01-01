
.code64
.section .data
.globl HV_DOORBELL_ADDR // *const *const HVDoorbell
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

.globl hv_handler
hv_handler:
  clac

  pushq 	$0
  pushq	  %rax
  pushq	  %rbx
  pushq	  %rcx

  testl   $0x200, ({EXCEP_FLAGS_OFF} - {EXCEP_RCX_OFF})(%rsp)
  jnz    .Lhv_handler_process_hv

  // Check whether the trap RIP is within the guest VMPL return window.
	leaq	  switch_vmpl_window_start(%rip), %rbx
	leaq	  switch_vmpl_window_end(%rip), %rcx
  // cmpq  	%rbx, %rax
  // jb	hv_not_vmpl_switch
	// cmp	%rcx, %rax
	// jae	hv_not_vmpl_switch

  // movq	({EXCEP_RIP_OFF} - {EXCEP_RCX_OFF})(%rsp), %rax
// Stub.
.Lprocess_pending_hv:
  ud2

.Lhv_handler_process_hv:
  pushq	  %rdx
	pushq	  %rsi
	pushq	  %rdi
	pushq 	%rbp
	pushq	  %r8
	pushq	  %r9
	pushq	  %r10
	pushq	  %r11
	pushq	  %r12
	pushq	  %r13
	pushq	  %r14
	pushq 	%r15

  xorl	  %edx, %edx
	// rdsspq	%rdx
	pushq	  %rdx

  // LOAD HV_DOORBELL_ADDR
  movq    HV_DOORBELL_ADDR(%rip), %rsi
  testq 	%rsi, %rsi
  jz      default_return
  movq    (%rsi), %rdi
  testq 	%rdi, %rdi
  jz      default_return

.Lcall_hv_doorbell:
  call    handle_hv_doorbell

.globl default_return
default_return:
	cli
  testb   $0x3, {EXCEP_CS_OFF}(%rsp) // check if interrupted in guest mode
  jnz     .Lhv_handler_return_guest

.Lreturn_to_all:
  // Check EFLAGS.IF
  testl   $0x200, {EXCEP_FLAGS_OFF}(%rsp)
  jz	    .Lbegin_iret_return

  movq    HV_DOORBELL_ADDR(%rip), %rdi
  testq   %rdi, %rdi
  jz     .Lbegin_iret_return
  movq    (%rdi), %rdi
  testq   %rdi, %rdi
  jz      .Lbegin_iret_return
  testw   $0x8000, (%rdi)
  jnz     .Lcall_hv_doorbell

.Lbegin_iret_return:
  addq      $8, %rsp    // skip ssp; currently we don't use it
  // begin iretq sequence
  popq       %r15
  popq       %r14
  popq       %r13
  popq       %r12
  popq       %r11
  popq       %r10
  popq       %r9
  popq       %r8
  popq       %rbp
  popq       %rdi
  popq       %rsi
  popq       %rdx
  popq       %rcx
  popq       %rbx
  popq       %rax

  // No error code is needed.
  addq    $8, %rsp

  iretq

.Lhv_handler_return_guest:
  // nothing to do
  jmp .Lreturn_to_all

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
