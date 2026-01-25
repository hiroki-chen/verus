.section .text.entry
.global _start

.code64

// !!!!! This is the entry point from the syscall !!!!!! //
_start:
  // The 'syscall' instruction disables interrupts and switches to Ring 0, but
  // it leaves the GS base pointing to User GS. We must switch to Kernel GS
  // immediately to access per-cpu data (even if we don't fully use it yet).
  swapgs
  // --------------------------------------------------------------------------
  // 2. Stack Switching (Critical for Safety)
  // --------------------------------------------------------------------------
  // We cannot trust the user's stack (RSP) for sensitive operations, and we
  // cannot yet use the standard Linux kernel stack because we haven't jumped
  // to the main kernel entry point yet.

  // Save the User RSP to our local storage using RIP-relative addressing.
  // This allows us to restore it later before handing control back to Linux.
  movq    %rsp, user_stack(%rip)

  // Switch RSP to our temporary private stack located within this page.
  // 'leaq' calculates the absolute address of 'deko_stack_top' at runtime.
  leaq    deko_stack_top(%rip), %rsp

  // Align the stack to 16 bytes.
  // The x86-64 System V ABI requires the stack to be 16-byte aligned before
  // any 'call' instructions. Although we don't 'call' C functions here,
  // it is best practice for stability and prevents #GP on SSE instructions.
  andq    $-16, %rsp

  // --------------------------------------------------------------------------
  // 3. Save Volatile Registers
  // --------------------------------------------------------------------------
  // We are about to perform a VMMCALL (Hypercall), which clobbers RAX, RCX, and RDX.
  // We must save the original values (which contain syscall arguments) to restore them later.
  pushq   %rdi  // [RSP+32] Original Arg 1
  pushq   %rax  // [RSP+24] Original Syscall No
  pushq   %rdx  // [RSP+16] Original Arg 3
  pushq   %rcx  // [RSP+8]  Original RIP (Return Address)
  pushq   %r11  // [RSP+0]  Original RFLAGS

prepare_syscall_body:
// Prepare the syscall body.
  xorq     %rdx, %rdx  // Clear RDX for use as pointer
  // Clear the syscall body area first (optional, for safety).
  leaq     deko_syscall_body(%rip), %rdx  // Pointer to syscall body
  movq     %rdx, %rdi
  movq     $0x0, %rax
  movq     $0x50, %rcx               // Size of syscall body (80 bytes)
  rep stosb

  movq     24(%rsp), %rax                 // Syscall number
  movq     %rax, 0x0(%rdx)                // Syscall number in body

  movq     32(%rsp), %rdi          // Arg 1
  movq     %rdi, 0x8(%rdx)         // Arg 1 in body
  movq     %rsi, 0x10(%rdx)        // Arg 2

  movq     16(%rsp), %rax          // Arg 3
  movq     %rax, 0x18(%rdx)        // Arg 3 in body

  movq     %r10, 0x20(%rdx)        // Arg 4
  movq     %r8, 0x28(%rdx)         // Arg 5
  movq     %r9, 0x30(%rdx)         // Arg 6

  movq     8(%rsp), %rcx          // Original RIP
  movq     %rcx, 0x38(%rdx)        // Return RIP in body

  movq     0(%rsp), %r11          // Original RFLAGS
  movq     %r11, 0x40(%rdx)        // Return

  movq     %rdx, %rdi               // Pointer to syscall body
  call     deko_ifc_entry

// Original entry.

deko_trampoline_end:

.data
.global user_stack
.global deko_trampoline_start
.global deko_stack_bottom
.global deko_stack_top
.align 8
user_stack:
  .quad 0x0    // [Runtime Storage] We save the user's RSP here temporarily.
deko_syscall_body:
  .fill 0x50, 1, 0x0 
.align 16
deko_stack_bottom:
  // Reserve 16KB (0x1000 bytes) for the deko stack.
  // The stack grows downwards (from High address to Low address).
  .fill 0x4000, 1, 0x0

deko_stack_top:
  // The RSP will point here initially.
  // When we PUSH, RSP decrements towards 'deko_stack_bottom'.

.align 8
deko_heap_bottom:
  // Reserve 256KB (0x1000 bytes) for the deko heap.
  .fill 0x40000, 1, 0x0
deko_heap_top:
  // The heap grows upwards (from Low address to High address).
