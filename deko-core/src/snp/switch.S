.pushsection .text.entry, "ax"

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

.popsection
