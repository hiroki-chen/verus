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
.global deko_ifc_engine_entry

deko_trampoline_start:
  // ============================================================================
  // 0. Filter out meaningless syscalls early
  // ============================================================================
  cmpq   $511, %rax
  ja     continue_analysis

  btq    %rax, filter_bitmap(%rip)
  jc    back_to_linux

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

prepare_syscall_body:
  // Prepare the syscall body.
  xorq     %rdi, %rdi  // Clear rdi for use as pointer
  // Clear the syscall body area first (optional, for safety).
  leaq     deko_syscall_body(%rip), %rdi  // Pointer to syscall body
  movq     $0x0, %rax
  movq     $SYSCALL_BODY_SIZE, %rcx               // Size of syscall body (80 bytes)
  rep stosb

  movq     24(%rsp), %rax                 // Syscall number
  movq     %rax, 0x0(%rdi)                // Syscall number in body

  movq     32(%rsp), %rax          // Arg 1
  movq     %rax, 0x8(%rdi)         // Arg 1 in body
  movq     %rsi, 0x10(%rdi)        // Arg 2

  movq     16(%rsp), %rax          // Arg 3
  movq     %rax, 0x18(%rdi)        // Arg 3 in body

  movq     %r10, 0x20(%rdi)        // Arg 4
  movq     %r8, 0x28(%rdi)         // Arg 5
  movq     %r9, 0x30(%rdi)         // Arg 6

  movq     8(%rsp), %rax          // Original RIP
  movq     %rax, 0x38(%rdi)        // Return RIP in body

  movq     0(%rsp), %r11          // Original RFLAGS
  movq     %r11, 0x40(%rdi)        // Return

  movq     %cr3, %rax
  movq     %rax, 0x48(%rdi)        // Current CR3

call_ifc:
  movq    deko_ifc_engine_entry(%rip), %rax
  testq   %rax, %rax
  je      1f                     // If IFC engine address is NULL, error out.
  
  callq   *%rax                   // Call IFC engine

  testq   %rax, %rax
  je      2f

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

  // TODO: Here we MAY need a way to catch sysret.

// ============================================================================
// Data & Stack Section
// ============================================================================
// This data is embedded directly into the code page.
// We align to 8 or 16 bytes to prevent unaligned memory access penalties.

.align 8
deko_trampoline_data_entry:
  .quad 0x0    // [Runtime Patch] C code writes the original LSTAR address here.
deko_ifc_engine_entry:
  .quad 0x0    // [Runtime Patch] C code writes the IFC engine entry address here.

.align 64
// Bitmap to filter syscalls (0-255) that do not need analysis.
filter_bitmap:
  // [0-63]:    0
  .quad 0x0000000000000000

  // [64-127]:  0
  .quad 0x0000000000000000

  // [128-191]: 
  .quad 0x0000000000000000
  
  // [192-255]:  0
  .quad 0x0000000000000000
  
  // [256-319]:  0
  .quad 0x0000000000000000
  
  // [320-383]:  0
  .quad 0x0000000000000000

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

// this is called by the guest kernel on execve to call the monitor
// to launch a new privileged process.
.global deko_sysret_trampoline
deko_sysret_trampoline:
  // do a naked vmmcall and let kvm handle the rest
  // wrmsr is not allowed in guest mode.
  vmmcall

  // Note: need to know if the program has been terminated.

  // jmp deko_sysret_trampoline

  // if we return here, just exit the guest.

  movq %rax, %rdi
  movq $60, %rax
  syscall

deko_trampoline_end:
