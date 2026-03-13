// SPDX-License-Identifier: MIT
//
// Copyright (c) 2024 SUSE LLC
// Copyright (c) 2025-2026 Hiroki Chen
//
// Author: Joerg Roedel <jroedel@suse.de>
//         Hiroki Chen <haobchen@iu.edu>

.equ USER_CS, 0x1b
.equ USER_SS, 0x23
.equ DEKO_VMPL1_KERN, 0xde
.equ DEKO_VMPL1_USER, 0xdf
.equ HV_DB_TRACE_SLOT0_OFF, 8
.equ HV_DB_TRACE_SLOT1_OFF, 16
.equ HV_DB_TRACE_SLOT2_OFF, 24
.equ HV_DB_TRACE_SLOT3_OFF, 32
.equ HV_DB_TRACE_SLOT4_OFF, 40
.equ HV_DB_TRACE_SLOT5_OFF, 48
.equ HV_DB_TRACE_SLOT6_OFF, 56

.macro LOAD_HV_DOORBELL_ADDR dest_reg

	rdtscp
	movq %rcx, %rax
	shrl $24, %ecx
	cmpl $DEKO_VMPL1_KERN, %ecx
	je 1f
	cmpl $DEKO_VMPL1_USER, %ecx
	je 1f

	movq HV_DOORBELL_ADDR(%rip), \dest_reg

	jmp 2f

1:
	// Calculate the address of this base addr.
	andl $0xFFF, %eax

	shlq $21, %rax    // %rax = id * 0x200000
	movq HV_DOORBELL_ADDR_VMPL1(%rip), \dest_reg
	addq %rax, \dest_reg
	addq ${DEKO_DOORBELL_CTX_OFFSET}, \dest_reg

2:

.endm

.code64

.section .data
.globl HV_DOORBELL_ADDR
.globl HV_DOORBELL_ADDR_VMPL1
.globl HV_SYSRET_WINDOW_START
.globl HV_SYSRET_WINDOW_END
HV_DOORBELL_ADDR:
	.quad 0
HV_DOORBELL_ADDR_VMPL1:
	.quad 0
HV_SYSRET_WINDOW_START:
	.quad 0
HV_SYSRET_WINDOW_END:
	.quad 0

.globl HV_TRACE_IRET_HITS
.globl HV_TRACE_IRET_FRAME_RSP
.globl HV_TRACE_IRET_FRAME_RIP
.globl HV_TRACE_RESTART_HITS
.globl HV_TRACE_RESTART_OLD_FRAME_RSP
.globl HV_TRACE_RESTART_NEW_FRAME_RSP
.globl HV_TRACE_RESTART_FRAME_RIP
HV_TRACE_IRET_HITS:
	.quad 0
HV_TRACE_IRET_FRAME_RSP:
	.quad 0
HV_TRACE_IRET_FRAME_RIP:
	.quad 0
HV_TRACE_RESTART_HITS:
	.quad 0
HV_TRACE_RESTART_OLD_FRAME_RSP:
	.quad 0
HV_TRACE_RESTART_NEW_FRAME_RSP:
	.quad 0
HV_TRACE_RESTART_FRAME_RIP:
	.quad 0

.globl DEBUG
DEBUG:
  .byte 0

.extern deko_async_timer_pre_iret_hook

.pushsection .entry.text, "ax"

// The #HV handler is coded specially in order to deal with control flow
// alterations that may be required based on when the #HV arrives.  If the #HV
// arrives from a context in which interrupts are enabled, then the #HV can
// be handled immediately.  In general, if the #HV arrives from a context in
// which interrupts are disabled, processing is postponed to a point in time
// when interrupt processing is safe.  However, there are two cases in which
// #HV processing is required even when interrupts are disabled.
// 1. The #HV arrives just before a return to the guest VMPL.  In this case,
//    the return to the guest VMPL must be cancelled so the #HV can be handled
//    immediately.  Otherwise, if the return to the guest occurs while the #HV
//    remains pending, it will remain pending until the next time the SVSM
//    is reentered, which could block delivery of critical events while the
//    guest is executing.
// 2. The #HV arrives while preparing to execute IRET to return to a context
//    in which interrupts are enabled.  If such an #HV is not handled, then
//    it will remain pending indefinitely, which could block delivery of
//    critical events.  When an #HV arrives at a time that the IRET is
//    is committed to complete, the #HV handler will "take over" the
//    exception context established previously (the one from which the IRET
//    intends to return).  In this case, the #HV handler will complete
//    processing and will perform the IRET to the point of the original
//    exception.
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
	// If the trap RIP is within the SYSRET window, postpone #HV until
	// the return path completes and interrupts can be handled normally.
	movq	HV_SYSRET_WINDOW_START(%rip), %rbx
	testq	%rbx, %rbx
	jz	0f
	cmpq	%rbx, %rax
	jb	0f
	movq	HV_SYSRET_WINDOW_END(%rip), %rcx
	cmpq	%rcx, %rax
	jb	postpone_hv
0:
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
	// Update RIP on the shadow stack to the cancel point.
	jmp 2f
	rdsspq	%rax
	wrssq	%rcx, 8(%rax)
2:
	// Defer any further processing until interrupts can be processed.
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
	jmp 2f
	movl	$3, %eax
	incsspq	%rax
2:
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
	incq	HV_TRACE_RESTART_HITS(%rip)
	movq	({EXCEP_RSP_OFF} - {EXCEP_FRAME_OFF})(%rcx), %rax
	movq	%rax, HV_TRACE_RESTART_OLD_FRAME_RSP(%rip)
	leaq	-4*8(%rcx), %rax
	movq	%rax, HV_TRACE_RESTART_NEW_FRAME_RSP(%rip)
	movq	({EXCEP_RIP_OFF} - {EXCEP_FRAME_OFF})(%rcx), %rax
	movq	%rax, HV_TRACE_RESTART_FRAME_RIP(%rip)
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
	jmp 2f
	movl	$3, %eax
	incsspq	%rax
2:

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
	jmp 3f
	rdsspq	%rcx
	wrssq	%rax, 8(%rcx)
3:
	// At this point, only the dummy error code and first three registers
	// have been pushed onto the stack.  Push the remainder to construct a
	// full exception context.
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
	# rdsspq is a nop when shadow stacks are not supported. Make sure that
	# rdx is 0 if that's the case.
	xorl	%edx, %edx
	rdsspq	%rdx
	pushq	%rdx
handle_as_hv:
	LOAD_HV_DOORBELL_ADDR %rsi

	testq	%rsi, %rsi
	jz	default_return
	movq	(%rsi), %rdi
	testq	%rdi, %rdi
	jz	default_return

handle_as_hv_with_doorbell:
	movq	HV_TRACE_IRET_HITS(%rip), %rax
	movq	%rax, HV_DB_TRACE_SLOT0_OFF(%rdi)
	movq	HV_TRACE_RESTART_HITS(%rip), %rax
	movq	%rax, HV_DB_TRACE_SLOT1_OFF(%rdi)
	movq	HV_TRACE_IRET_FRAME_RSP(%rip), %rax
	movq	%rax, HV_DB_TRACE_SLOT2_OFF(%rdi)
	movq	HV_TRACE_IRET_FRAME_RIP(%rip), %rax
	movq	%rax, HV_DB_TRACE_SLOT3_OFF(%rdi)
	movq	HV_TRACE_RESTART_OLD_FRAME_RSP(%rip), %rax
	movq	%rax, HV_DB_TRACE_SLOT4_OFF(%rdi)
	movq	HV_TRACE_RESTART_NEW_FRAME_RSP(%rip), %rax
	movq	%rax, HV_DB_TRACE_SLOT5_OFF(%rdi)
	movq	HV_TRACE_RESTART_FRAME_RIP(%rip), %rax
	movq	%rax, HV_DB_TRACE_SLOT6_OFF(%rdi)
	callq	handle_hv_doorbell
	// fall through to default_return

.globl default_return
default_return:
	// Ensure that interrupts are disabled before attempting any return.
	cli
	testb	$3, {EXCEP_CS_OFF}(%rsp) // Check CS RPL in exception frame
	jnz	return_user
return_all_paths:
	// If interrupts were previously available, then check whether any #HV
	// events are pending.  If so, proceed as if the original trap was
	// #HV.
	testl	$0x200, {EXCEP_FLAGS_OFF}(%rsp) // check EFLAGS.IF in exception frame
	jz	begin_iret_return

	LOAD_HV_DOORBELL_ADDR %rsi

	test	%rsi, %rsi
	jz	begin_iret_return
	movq	(%rsi), %rdi
	test	%rdi, %rdi
	jz	begin_iret_return
	testb	$0xff, (%rdi)          // vector != 0
	jnz	iret_return_window
	testw	$0x8000, (%rdi)        // NoFurtherSignal set
	// Pending is signaled by either vector!=0 or NoFurtherSignal.
	// After this point, all code must execute within this instruction
	// range to ensure that the #HV handler will detect arrivals that
	// race with the return path.
iret_return_window:
	setnz	%bl
	incq	HV_TRACE_IRET_HITS(%rip)
	movq	{EXCEP_RSP_OFF}(%rsp), %rax
	movq	%rax, HV_TRACE_IRET_FRAME_RSP(%rip)
	movq	{EXCEP_RIP_OFF}(%rsp), %rax
	movq	%rax, HV_TRACE_IRET_FRAME_RIP(%rip)
	testb	%bl, %bl
	jnz	handle_as_hv_with_doorbell
begin_iret_return:
	// Reload registers without modifying the stack pointer so that if #HV
	// occurs within this window, the saved registers are still intact.
	movq	{EXCEP_R15_OFF}(%rsp), %r15
	movq	{EXCEP_R14_OFF}(%rsp), %r14
	movq	{EXCEP_R13_OFF}(%rsp), %r13
	movq	{EXCEP_R12_OFF}(%rsp), %r12
	movq	{EXCEP_R11_OFF}(%rsp), %r11
	movq	{EXCEP_R10_OFF}(%rsp), %r10
	movq	{EXCEP_R9_OFF}(%rsp), %r9
	movq	{EXCEP_R8_OFF}(%rsp), %r8
	movq	{EXCEP_RBP_OFF}(%rsp), %rbp
	movq	{EXCEP_RDI_OFF}(%rsp), %rdi
	movq	{EXCEP_RSI_OFF}(%rsp), %rsi
	movq	{EXCEP_RDX_OFF}(%rsp), %rdx
	movq	{EXCEP_RCX_OFF}(%rsp), %rcx
	movq	{EXCEP_RBX_OFF}(%rsp), %rbx
	movq	{EXCEP_RAX_OFF}(%rsp), %rax

	// Skip error code.
	addq	${EXCEP_FRAME_OFF}, %rsp

default_iret:
	iretq

return_user:
	callq	deko_async_timer_pre_iret_hook
	jmp	return_all_paths

.globl return_new_task
return_new_task:
	call	setup_user_task
	jmp	default_return

.popsection
