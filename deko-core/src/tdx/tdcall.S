#
# _td_call(args: *mut TdcallArgs) -> u64
# First argument is in %rdi.
# Return value must be in %rax.
#

.global _td_call

.equ RAX_OFFSET, 0x00
.equ RCX_OFFSET, 0x08
.equ RDX_OFFSET, 0x10
.equ R8_OFFSET,  0x18
.equ R9_OFFSET,  0x20
.equ R10_OFFSET, 0x28
.equ R11_OFFSET, 0x30
.equ R12_OFFSET, 0x38
.equ R13_OFFSET, 0x40

_td_call:
  endbr64

  # This function implements the TDCALL instruction for Intel TDX.
  # --- Function Prologue ---
  # Set up the stack frame according to System V AMD64 ABI
  pushq %rbp
  movq  %rsp, %rbp

  # Save callee-saved registers that we will modify.
  # r12-r15 and rbx must be preserved by this function.
  pushq %rbx
  pushq %r12
  pushq %r13
  pushq %r14
  pushq %r15

  # --- Function Body ---

  # Check if the input pointer (%rdi) is null.
  # This is excellent practice.
  cmpq $0, %rdi
  je _td_call_error_exit # If null, jump to the exit with an error code.

  # Load registers from the TdcallArgs struct pointed to by %rdi.
  # This is the "input" stage.
  movq RAX_OFFSET(%rdi), %rax
  movq RCX_OFFSET(%rdi), %rcx
  movq RDX_OFFSET(%rdi), %rdx
  movq R8_OFFSET(%rdi),  %r8
  movq R9_OFFSET(%rdi),  %r9
  movq R10_OFFSET(%rdi), %r10
  movq R11_OFFSET(%rdi), %r11
  movq R12_OFFSET(%rdi), %r12
  movq R13_OFFSET(%rdi), %r13

  # DEBUG: Uncomment this 'ud2' to check if the registers loaded correctly.
  # ud2

  # Perform the actual TDCALL. This is the VMCALL instruction with an
  # operand-size override prefix.
  .byte 0x66, 0x0f, 0x01, 0xcc

  # Check the return code from TDCALL in %rax. A non-zero value indicates an error.
  cmpq $0, %rax
  jnz _td_call_success_exit # If error, jump to exit. The error code is already in %rax.

  # --- Success Path ---
  # TDCALL succeeded, copy the output registers back to the struct.
  # Note: You were copying %rax back, but the TDCALL spec says that
  # on success, %rax is 0. So we only need to copy the other registers
  # which may have been modified.
  movq %rcx, RCX_OFFSET(%rdi)
  movq %rdx, RDX_OFFSET(%rdi)
  movq %r8,  R8_OFFSET(%rdi)
  movq %r9,  R9_OFFSET(%rdi)
  movq %r10, R10_OFFSET(%rdi)
  movq %r11, R11_OFFSET(%rdi)
  movq %r12, R12_OFFSET(%rdi)
  movq %r13, R13_OFFSET(%rdi)
  # The success return code (0) is already in %rax.

_td_call_success_exit:
  # --- Function Epilogue ---
  # Restore saved registers in reverse order of pushing.
  popq %r15
  popq %r14
  popq %r13
  popq %r12
  popq %rbx

  # Tear down the stack frame and return.
  leave
  ret

_td_call_error_exit:
  # Set an error return code in %rax to indicate null pointer.
  # A value like -1 (0xffffffffffffffff) is a common choice.
  movq $-1, %rax
  # Now jump to the common epilogue to restore registers and return.
  jmp _td_call_success_exit
