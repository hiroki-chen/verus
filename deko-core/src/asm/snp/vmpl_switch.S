// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
// Copyright (c) 2025-2026 Hiroki Chen
//
// Author: Joerg Roedel <jroedel@suse.de>
//         Hiroki Chen  <haobchen@iu.edu>

.pushsection .text.entry, "ax"
.globl hv_redirect_window_start
hv_redirect_window_start:

.globl switch_to_vmpl_unsafe
switch_to_vmpl_unsafe:
    /* Upon entry,
     * rdi = pointer to the HV doorbell page
     * esi = target VMPL
     * rdx = value to place in rax before vmmcall
     */

    jmp switch_vmpl_proceed

    /* From this point until the vmgexit, if a #HV arrives, the #HV handler
     * must prevent the VMPL transition. */
.globl switch_vmpl_window_start
switch_vmpl_window_start:
    jnz switch_vmpl_cancel

switch_vmpl_proceed:
    /* Use the MSR-based VMPL switch request to avoid any need to use the
      * GHCB page.  Run VMPL request is 0x16 and response is 0x17. */
    movq %rdx, %r11
    movl $0x16, %eax
    movl %esi, %edx
    movl $0xc0010130, %ecx
    wrmsr
    movq %r11, %rax
    rep; vmmcall

.globl switch_vmpl_window_end
switch_vmpl_window_end:
    /* Verify that the request was honored.  ECX still contains the MSR
      * number. */
    rdmsr
    andl $0xFFF, %eax
    cmpl $0x17, %eax
    jnz switch_vmpl_failed
    xorl %eax, %eax
    ret

switch_vmpl_failed:
    // movl $2, %eax
    ret

.globl switch_vmpl_cancel
switch_vmpl_cancel:
    movl $1, %eax
    ret

    /* Idle halt is placed here as well, because idle halt requires
      * detection in the #HV handler to determine whether the HLT should be
      * skipped.  Placing this code here means that a single quick check can
      * be made to determine whether RIP is in a host exiting window (switch
      * VMPL or HLT) before needing to make a further determination about
      * which window was executing. */
.globl snp_idle_halt
snp_idle_halt:
    /* Upon entry, rdi = pointer to the HV doorbell page.
      * Check if NoFurtherSignal is set (bit 15 of the first word of the
      * #HV doorbell page).  If so, skip the halt. */
    test %rdi, %rdi
    jz idle_halt_proceed
    testw $0x8000, (%rdi)

    /* From this point until the HLT, if a #HV arrives, the #HV handler
      * must prevent the halt. */
.globl idle_halt_window_start
idle_halt_window_start:
    jnz idle_halt_window_end
idle_halt_proceed:
    sti
  
.globl snp_idle_hlt_instruction
snp_idle_hlt_instruction:
    hlt

.globl idle_halt_window_end
idle_halt_window_end:
    cli
    ret

.globl hv_redirect_window_end
hv_redirect_window_end:

.popsection
