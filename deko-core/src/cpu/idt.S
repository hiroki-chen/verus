// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

.text

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
