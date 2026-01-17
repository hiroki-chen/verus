// Deko SYSCALL trampoline code.
//
// This code runs in guest context (CPL0 and VMPL > 0 + RX ONLY).

// We need to make sure that this piece of code
// is position independent, so we use RIP-relative addressing only.
.section .data
.global deko_trampoline_start
.global deko_trampoline_end
.global deko_trampoline_data_entry

deko_trampoline_start:
  // Syscall Prelude: must be CPL0
  // Guest is executing at VMPL > 0!!!!!!
  swapgs

  // Save USER RSP
  movq    %rsp, user_stack(%rip)
  // Swap to our own stack.
  leaq    deko_stack_top(%rip), %rsp
  andq    $-16, %rsp
  // Save registers that we will clobber
  pushq   %rax
  pushq   %rdx
  pushq   %rcx
  movl    $0x16, %eax             // VMPL_RUN for Deko service calls
  xorl    %edx, %edx              // VMPL 0
  movl    $0xc0010130, %ecx   // MSR_SEV_GHCB

  // Now set up the GHCB and make the VMMCALL
  // Now switch to VMPL 0
  wrmsr
  rep; vmmcall
  rdmsr

  cmpq    $0x17, %rax
  je      2f

  // fallthrough to error.
1:
  ud2
  hlt
2:
  popq   %rcx
  popq   %rdx
  popq   %rax

  movq   user_stack(%rip), %rsp
  swapgs

  // Continue execution at the original syscall entry point
  jmp     *deko_trampoline_data_entry(%rip)

.align 8
deko_trampoline_data_entry:
  .quad 0x0    // Placeholder for original syscall entry pointer
deko_trampoline_end:

deko_stack_bottom:
  .fill 0x1000, 1, 0x0
deko_stack_top:

user_stack:
  .quad 0x0    // Placeholder for user RSP storage
