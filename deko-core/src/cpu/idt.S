// SPDX-License-Identifier: MIT
//
// Copyright (c) 2024 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

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

// The #HV handler is coded specially in order to deal with control flow
// alterations that may be required based on when the #HV arrives.  If the #HV
// arrives from a context in which interrupts are enabled, then the #HV can
// be handled immediately.
// In general, if the #HV arrives from a context in which interrupts are disabled,
// processing is postponed to a point in time when interrupt processing is safe. 
// However, there are two cases in which #HV processing is required even when
// interrupts are disabled.
//
// 1. The #HV arrives just before a return to the guest VMPL.  In this case,
//    the return to the guest VMPL must be cancelled so the #HV can be handled
//    immediately.
// 2. The #HV arrives while preparing to execute IRET to return to a context
//    in which interrupts are enabled.
.globl hv_handler
hv_handler:
  clac

  // Push a dummy error code, and only three registers as scratch
	// registers.  If no #HV processing is required, then only these three
	// registers will need to be popped.
	pushq	$0
	pushq	%rax
	pushq	%rbx
	pushq	%rcx
	// Fetch RIP from the trap frame.
	movq	({EXCEP_RIP_OFF} - {EXCEP_RCX_OFF})(%rsp), %rax
  // Check whether interrupts were enabled at the time of #HV.  If so,
	// commit to processing all #HV events immediately.
	testl	$0x200, ({EXCEP_FLAGS_OFF} - {EXCEP_RCX_OFF})(%rsp)
	jnz	continue_hv
// Check whether the trap RIP is within any code that may require
	// RIP redirection
	leaq	hv_redirect_window_start(%rip), %rbx
	leaq	hv_redirect_window_end(%rip), %rcx
	cmp	%rbx, %rax
	jb	hv_no_rip_redirect
	cmp	%rcx, %rax
	jae	hv_no_rip_redirect
	// Check whether the trap RIP is within the guest VMPL return window.
	leaq	switch_vmpl_window_start(%rip), %rbx
	leaq	switch_vmpl_window_end(%rip), %rcx
	cmp	%rbx, %rax
	jb	hv_not_vmpl_switch
	cmp	%rcx, %rax
	jae	hv_not_vmpl_switch
	// RIP is in the return window, so update RIP to the cancel point.
	leaq	switch_vmpl_cancel(%rip), %rcx

update_hv_rip:
	movq	%rcx, ({EXCEP_RIP_OFF} - {EXCEP_RCX_OFF})(%rsp)
	jmp	postpone_hv

hv_not_vmpl_switch:
	// Check whether the trap RIP is within the idle halt window
	leaq	idle_halt_window_start(%rip), %rbx
	leaq	idle_halt_window_end(%rip), %rcx
	cmp	%rbx, %rax
	jb	hv_no_rip_redirect
	cmp	%rcx, %rax
	// If RIP is in the return window, jump back to update RIP.  Rcx
	// already contains the correct target RIP.
	jb	update_hv_rip

hv_no_rip_redirect:
	// Load the RSP value that was live at the time of the #HV.
	movq	({EXCEP_RSP_OFF} - {EXCEP_RCX_OFF})(%rsp), %rcx
	// Check to see whether this interrupt occurred on the IRET path
	leaq	iret_return_window(%rip), %rbx
	cmp	%rbx, %rax
	jb	postpone_hv
	leaq	default_iret(%rip), %rbx
	cmp	%rbx, %rax
	ja	postpone_hv
	// RIP is within the IRET sequence, so the IRET should be aborted, and
	// the previous exception should be handled as if it were #HV.  At this
	// point, there are two possibilities.  If RIP is before the IRET
	// instruction itself, then the RSP at the time of #HV exception
	// points to the register context that was established for the previous
	// exception.  In that case, the current RSP can be changed to point
	// to that exception context, and the #HV can be handled using that
	// register context, and when #HV processing completes, the subsequent
	// end-of-interrupt flow will restore the context at the time of the
	// previous exception.  On the other hand, if RIP has advanced to the
	// point of the IRET instruction itself, then all of the registers
	// have already been reloaded with the previous exception context,
	// and the RSP at the time of #HV points at the stack frame that
	// would be consumed by the IRET instruction.  In that case, a new
	// exception context will need to be constructed.  At this point,
	// EFLAGS.ZF=1 if the previous RIP was at the IRET instruction.
	jz	restart_hv
	// Check to see whether interrupts were enabled at the time the
	// previous exception was taken.  If not, no further processing is
	// required.  This could not be performed before the RIP check because
	// the previous RIP determines where to find the previous EFLAGS.IF
	// value on the stack.
	testl	$0x200, {EXCEP_FLAGS_OFF}(%rcx)
	jz	postpone_hv
	// Switch to the stack pointer from the previous exception, which
	// points to the register save area, and continue with #HV
	// processing.
	movq	%rcx, %rsp
	// Pop the current stack frame, so that the previous stack frame sits
	// on top of the shadow stack.
	jmp	handle_as_hv

postpone_hv:
	popq	%rcx
	popq	%rbx
	popq	%rax
	// Skip error code.
	addq	$8, %rsp
	iretq

restart_hv:
	// The previous RIP was on an IRET instruction.  Before moving forward
	// with #HV processing, check to see whether interrupts were enabled at
	// the time the previous exception was taken.  If not, no further
	// processing is required.  This could not be done when RIP was
	// checked because the stack location of the previous EFLAGS.IF value
	// was not known until RIP was determined to be at the IRET
	// instruction.
	//
	// At this point, RCX holds the stack pointer at the time of the
	// IRET that was aborted.  In other words, it is pointing to
	// &X86ExceptionContext.frame.
	testl	$0x200, ({EXCEP_FLAGS_OFF} - {EXCEP_FRAME_OFF})(%rcx)
	jz	postpone_hv
	// Since interrupts were enabled in the previous exception frame,
	// #HV processing is now required.  The previous RSP points to the
	// exception frame (minus error code) as it would be consumed by
	// IRET.  In order to set up a new exception context, the three
	// registers that were saved upon entry to the #HV handler will need to
	// be copied to the top of the stack (adjacent to the space for a
	// dummy erro code).  Then, the stack pointer will be loaded with
	// the previous RSP and the remaining register state will be pushed
	// normally to create a complete exception context reflecting the
	// register state at the time of the exception that was returning at
	// the time the #HV arrived.
	//
	// The first QWORD below the RCX pointer is reserved for the dummy
	// error code, then the three QWORDS below that will hold the RAX, RBX,
	// and RCX values, which are presently stored in the top three QWORDs
	// of the current stack.  Copy them back to the previous exception
	// context and start reconstructing (or "taking over") it.
	movq	0*8(%rsp), %rax
	movq	%rax, -4*8(%rcx)
	movq	1*8(%rsp), %rax
	movq	%rax, -3*8(%rcx)
	movq	2*8(%rsp), %rax
	movq	%rax, -2*8(%rcx)
	// Load the previous stack pointer and continue reconstruction at RDX.
	leaq	-4*8(%rcx), %rsp
	// Pop the current stack frame, so that the previous stack frame sits
	// on top of the shadow stack.

continue_hv:
	// Check to see whether RIP points at the idle halt instruction.  If
	// so, skip the HLT because the interrupt will be handled now.  This
	// effectively emulates interrupt window behavior.  At this point,
	// rax contains the exception RIP.
	leaq	snp_idle_hlt_instruction(%rip), %rcx
	cmpq	%rax, %rcx
	jne	3f
	incq	%rax
	movq	%rax, ({EXCEP_RIP_OFF} - {EXCEP_RCX_OFF})(%rsp)
	// Update RIP on the shadow stack to the cancel point.
	// At this point, only the dummy error code and first three registers
	// have been pushed onto the stack.  Push the remainder to construct a
	// full exception context.
3:
	pushq	%rdx
	pushq	%rsi
	pushq	%rdi
	pushq	%rbp
	pushq	%r8
	pushq	%r9
	pushq	%r10
	pushq	%r11
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	xorl	%edx, %edx
	pushq	%rdx
handle_as_hv:
	// Load the address of the #HV doorbell page.  The global address
	// might not yet be configured, and the per-CPU page might also not
	// yet be configured, so only process events if there is a valid
	// doorbell page.
	movq	HV_DOORBELL_ADDR(%rip), %rsi
	testq	%rsi, %rsi
	jz	default_return
	movq	(%rsi), %rdi
	testq	%rdi, %rdi
	jz	default_return

handle_as_hv_with_doorbell:
  call    handle_hv_doorbell

.globl default_return
default_return:
	cli
  testb   $0x3, {EXCEP_CS_OFF}(%rsp) // check if interrupted in guest mode
  jnz     return_user

return_all_paths:
  // Check EFLAGS.IF
  testl   $0x200, {EXCEP_FLAGS_OFF}(%rsp)
  jz	    begin_iret_return

  movq    HV_DOORBELL_ADDR(%rip), %rdi
  testq   %rdi, %rdi
  jz      begin_iret_return
  movq    (%rdi), %rdi
  testq   %rdi, %rdi
  jz      begin_iret_return
  testw   $0x8000, (%rdi)

iret_return_window:
  jnz     handle_as_hv_with_doorbell

begin_iret_return:
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

default_iret:
	iretq

return_user:
	// Put user-mode specific return code here
	jmp	return_all_paths

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
