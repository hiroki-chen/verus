.pushsection .text.entry, "ax"

.globl hv_redirect_window_start
hv_redirect_window_start:


.globl switch_to_vmpl_unsafe
switch_to_vmpl_unsafe:
    /* From this point until the vmgexit, if a #HV arrives, the #HV handler
      * must prevent the VMPL transition. */
    cmpl $3, %edi
    .globl switch_vmpl_window_start
switch_vmpl_window_start:
    jg switch_vmpl_cancel

switch_vmpl_proceed:
    /* Use the MSR-based VMPL switch request to avoid any need to use the
      * GHCB page.  Run VMPL request is 0x16 and response is 0x17. */
    movl $0x16, %eax
    movl %edi, %edx
    movl $0xc0010130, %ecx
    wrmsr
    rep; vmmcall

    .globl switch_vmpl_window_end
switch_vmpl_window_end:
    /* Verify that the request was honored.  ECX still contains the MSR
      * number. */
    rdmsr
    andl $0xFFF, %eax
    cmpl $0x17, %eax
    jne switch_vmpl_cancel
    xorl %eax, %eax
    ret

    /* An aborted VMPL switch is treated as a successful switch. */
    .globl switch_vmpl_cancel
switch_vmpl_cancel:
    movl $1, %eax
    ret
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
