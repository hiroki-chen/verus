// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>
// Author: Hiroki Chen <haobchen@iu.edu>

.text

.globl deko_ifc_irq_reflection
deko_ifc_irq_reflection:
	pushq %rdi
	pushq %rsi

	movl  $0xc0010130, %ecx
	xorl  %edx, %edx
	movl  $0x16, %eax // VMPL_RUN
	wrmsr

	// todo: move the interrupt vector number into somewhere.
  // construct the SVSM call to reflect the interrupt.
	movabs $0x400000002, %rax
	// movq $<interrupt-vector>, %rdx

	rep; vmmcall

	rdmsr
	cmpl $0x17, %eax
	jne   1f

	popq %rsi
	popq %rdi
	iretq
1:
	// Error handling path.
	cli
	ud2
	hlt

// Let it die.
.globl deko_ifc_idt_handler_default
.globl deko_ifc_idt_handler_page_fault

deko_ifc_idt_handler_default:
  cli
  ud2
  hlt

deko_ifc_idt_handler_nmi:
	clac

	pushq	%rax
	pushq	%rbx
	pushq	%rcx
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
	xorl	%eax, %eax
	rdsspq	%rax
	pushq	%rax

	testl	$0x200, 0x98(%rsp)

	jz	.Lskip_nmi2
	sti
.Lskip_nmi2:
	movl	$2, %esi               // NMI Vector
	movq	%rsp, %rdi
	xorl	%edx, %edx
	call	deko_ifc_handler_nmi

deko_ifc_idt_handler_page_fault:
	clac

	pushq	%rax
	pushq	%rbx
	pushq	%rcx
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
	xorl	%eax, %eax
	rdsspq	%rax
	pushq	%rax

	testl	$0x200, 0x98(%rsp)

	jz	.Lskip_pf2
	sti
.Lskip_pf2:
	movl	$14, %esi               // Page Fault Vector
	movq	%rsp, %rdi
	xorl	%edx, %edx
	call	deko_ifc_handler_page_fault

	iretq

.globl stage2_generic_idt_handler
.globl stage2_generic_idt_handler_no_ghcb
stage2_generic_idt_handler:
stage2_generic_idt_handler_no_ghcb:
	ud2

generic_idt_handler_return:
	addq    $8, %rsp /* Skip ssp */

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

	addq    $8, %rsp /* Skip error code */
	iretq

.pushsection .entry.text, "ax"

		/* Early tage 2 handler array setup */
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

	pushq   $0 /* ssp */
	movq    %rsp, %rdi
	call    stage2_generic_idt_handler_no_ghcb
	jmp     generic_idt_handler_return

.popsection

.align 32

.globl stage2_idt_handler_array_no_ghcb
stage2_idt_handler_array_no_ghcb:
	i = 0
	.rept 32
	.align 32
	.if ((0x20027d00 >> i) & 1) == 0
	pushq   $0  /* Dummy error code */
	.endif
	pushq   $i  /* Vector Number */
	jmp     push_regs_no_ghcb
	i = i + 1
	.endr

.pushsection .entry.text, "ax"

/* Stage 2 handler array setup */
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
	jmp     generic_idt_handler_return

.popsection

.align 32
.globl stage2_idt_handler_array

stage2_idt_handler_array:
	i = 0
	.rept 32
	.align 32
	.if ((0x20027d00 >> i) & 1) == 0
	pushq   $0  /* Dummy error code */
	.endif
	pushq   $i  /* Vector Number */
	jmp     push_regs_stage2
	i = i + 1
	.endr

