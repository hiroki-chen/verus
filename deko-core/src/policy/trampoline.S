// ============================================================================
// Deko SYSCALL Trampoline Code
// ============================================================================
// Context:
//   - Runs in Guest Ring 0 (CPL0).
//   - Runs at a restricted VMPL (e.g., VMPL 1 or 2), attempting to contact VMPL 0.
//   - Memory Protection: The page containing this code must be mapped as RWX 
//     (Read/Write/Execute) because we save the RSP into a variable within this page.
//
// Key Constraints:
//   - Position Independent Code (PIC): We must use RIP-relative addressing for all
//     memory accesses because this code will be copied to an arbitrary physical page
//     (likely allocated via memblock or vmalloc) and mapped to a new virtual address.
//
// SERVES THE CONTAINER!!!
// ============================================================================

.equ PER_CPU_STACK_SIZE,   0x100
.equ SYSCALL_BODY_SIZE,    0x50
.equ USER_STACK_SAVE_SIZE, 0x8

.section .data
.global deko_trampoline_start
.global deko_trampoline_end
.global deko_trampoline_data_entry

deko_trampoline_start:
  // ============================================================================
  // 0. Filter out meaningless syscalls early
  // ============================================================================
  cmpq   $511, %rax
  ja     continue_analysis

  btq    %rax, filter_bitmap(%rip)
  jnc    back_to_linux

continue_analysis:

prepare_syscall:
  movq    %rsp, scratch_rsp(%rip)   // Save User RSP
  // switch to our temporary stack.
  // --------------------------------------------------------------------------
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

do_write_ghcb:
  // --------------------------------------------------------------------------
  // 4. Setup GHCB (Guest-Hypervisor Communication Block) Protocol
  // --------------------------------------------------------------------------
  // We are preparing to exit the guest context to talk to the higher privilege level (VMPL 0).

  // RAX = 0x16: The protocol ID for "VMPL_RUN" or your specific Deko service call.
  movl    $0x16, %eax

  // RDX = 0: Target VMPL level (VMPL 0).
  xorl    %edx, %edx

  // RCX = 0xC0010130: MSR_AMD64_SEV_ES_GHCB.
  // We write to this MSR to register the GHCB address or protocol info.
  movl    $0xc0010130, %ecx

  // --------------------------------------------------------------------------
  // 5. Execute VMGEXIT (VMMCALL)
  // --------------------------------------------------------------------------
  // Write the request to the MSR.
  wrmsr

prepare_syscall_body:
  // Prepare the syscall body.
  xorq     %rdx, %rdx  // Clear RDX for use as pointer
  // Clear the syscall body area first (optional, for safety).
  leaq     deko_syscall_body(%rip), %rdx  // Pointer to syscall body
  movq     %rdx, %rdi
  movq     $0x0, %rax
  movq     $SYSCALL_BODY_SIZE, %rcx               // Size of syscall body (80 bytes)
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

  movq     %cr3, %rax
  movq     %rax, 0x48(%rdx)        // Current CR3

do_vmm_call:
  // Now prepare the SVSM call parameters.
  movabsq $0x400000001, %rax
  // Trigger the VMEXIT. The hypervisor (or VMPL 0 handler) will intercept this.
  rep; vmmcall
  // Read back the result from the MSR (optional, depending on protocol).
  cmpq    $0, %rax
  jne 	  1f

  movl    $0xc0010130, %ecx
  rdmsr

  // --------------------------------------------------------------------------
  // 6. Check Result
  // --------------------------------------------------------------------------
  // Compare the returned value in RAX with expected success code (0x17).
  cmpq     $0x17, %rax
  je       2f

  // --------------------------------------------------------------------------
  // 7. Error Handling
  // --------------------------------------------------------------------------
  // If the hypercall failed, we cannot safely proceed.
  // UD2 triggers an "Undefined Instruction" exception (Kernel Panic).
  // HLT stops the CPU if UD2 is handled or ignored.
1:
  ud2
  hlt

  // --------------------------------------------------------------------------
  // 8. Restore State
  // --------------------------------------------------------------------------
2:
  // Restore the syscall arguments and context we saved earlier.
  // Order is LIFO (Last-In, First-Out).
  popq     %r11
  popq     %rcx
  popq     %rdx
  popq     %rax
  popq     %rdi

  // Restore User RSP from our saved location.
  movq    scratch_rsp(%rip), %rsp

back_to_linux:
  // --------------------------------------------------------------------------
  // 9. Handover to Linux Kernel
  // --------------------------------------------------------------------------
  // Jump to the original Linux LSTAR address.
  // The C setup code must populate 'deko_trampoline_data_entry' with the
  // address of the real 'entry_SYSCALL_64'.
  jmp     *deko_trampoline_data_entry(%rip)

  // TODO: Here we need to have a way to catch sysret.

// ============================================================================
// Data & Stack Section
// ============================================================================
// This data is embedded directly into the code page.
// We align to 8 or 16 bytes to prevent unaligned memory access penalties.

.align 8
deko_trampoline_data_entry:
  .quad 0x0    // [Runtime Patch] C code writes the original LSTAR address here.

.align 64
// Bitmap to filter syscalls (0-255) that do not need analysis.
filter_bitmap:
  // [0-63]: clone(56) | vfork(58) | execve(59)
  .quad 0x0D00000000000000

  // [64-127]:  0
  .quad 0x0000000000000000
  
  // [128-191]:  pivot_root(155)
  .quad 0x0000000008000000
  
  // [192-255]:  0
  .quad 0x0000000000000000
  
  // [256-319]:  0
  .quad 0x0000000000000000
  
  // [320-383]:  execveat (322) -> Bit 2 -> 0x4
  .quad 0x0000000000000004

  // [384-447]:  0
  .quad 0x0000000000000000

  // [448-511]:  0
  .quad 0x0000000000000000

  .quad 0x0
  .quad 0x0

.align 8
  // [Runtime Storage] We save the user's RSP here temporarily.
scratch_rsp:
  .fill USER_STACK_SAVE_SIZE, 1, 0x0
deko_syscall_body:
  .fill SYSCALL_BODY_SIZE, 1, 0x0 

.align 16
deko_stack_bottom:
  // This is the temporary stack for the trampoline code.
  // Once we jump into the IFC engine, the stack will be
  // replaced by its own.
  // The stack grows downwards (from High address to Low address).
  .fill PER_CPU_STACK_SIZE, 1, 0x0

deko_stack_top:
  // The RSP will point here initially.
  // When we PUSH, RSP decrements towards 'deko_stack_bottom'.
deko_trampoline_end:
