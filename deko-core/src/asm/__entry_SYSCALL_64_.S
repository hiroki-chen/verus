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

.equ PER_CPU_STACK_SIZE,   0x800
.equ SYSCALL_BODY_SIZE,    0x50
.equ USER_STACK_SAVE_SIZE, 0x8

.section .data
.global deko_trampoline_start
.global deko_trampoline_end
.global deko_trampoline_data_entry
.global deko_ifc_engine_entry
.global deko_sysret_window_start
.global deko_sysret_window_end

deko_trampoline_start:
  // ============================================================================
  // 0. Filter out meaningless syscalls early
  // ============================================================================
  cmpq   $511, %rax
  ja     continue_analysis

  // btq    %rax, filter_bitmap(%rip)
  // jc    back_to_linux

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
  // We must save the original values (which contain syscall arguments) to restore them later.
  pushq   %r11  // [RSP+64] Original RFLAGS
  pushq   %rcx  // [RSP+56] Original RIP
  pushq   %r9   // [RSP+48] Arg 6
  pushq   %r8   // [RSP+40] Arg 5
  pushq   %r10  // [RSP+32] Arg 4
  pushq   %rdx  // [RSP+24] Arg 3
  pushq   %rsi  // [RSP+16] Arg 2
  pushq   %rdi  // [RSP+8]  Arg 1
  pushq   %rax  // [RSP+0]  Syscall Number

prepare_syscall_body:
  // Prepare the syscall body.
  xorq     %rdi, %rdi  // Clear rdi for use as pointer
  // Clear the syscall body area first (optional, for safety).
  leaq     deko_syscall_body(%rip), %rdi  // Pointer to syscall body
  movq     $0x0, %rax
  movq     $SYSCALL_BODY_SIZE, %rcx               // Size of syscall body (80 bytes)
  cld
  rep stosb

  leaq     deko_syscall_body(%rip), %rdi

  movq     0(%rsp), %rax          
  movq     %rax, 0x0(%rdi)        // ax
  movq     8(%rsp), %rax          
  movq     %rax, 0x8(%rdi)        // di
  movq     16(%rsp), %rax         
  movq     %rax, 0x10(%rdi)       // si
  movq     24(%rsp), %rax         
  movq     %rax, 0x18(%rdi)       // dx
  movq     32(%rsp), %rax         
  movq     %rax, 0x20(%rdi)       // r10
  movq     40(%rsp), %rax         
  movq     %rax, 0x28(%rdi)       // r8
  movq     48(%rsp), %rax         
  movq     %rax, 0x30(%rdi)       // r9
  movq     56(%rsp), %rax         
  movq     %rax, 0x38(%rdi)       // original RIP
  movq     64(%rsp), %rax         
  movq     %rax, 0x40(%rdi)       // original RFLAGS

  movq     %cr3, %rax
  movq     %rax, 0x48(%rdi)       // current CR3

call_ifc:
  movq    deko_ifc_engine_entry(%rip), %rax

  callq   *%rax                   // Call IFC engine

  testq   %rax, %rax
  je      return_to_user

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
return_to_user:
deko_sysret_window_start:
  addq    $8, %rsp
  // Restore the syscall arguments and context we saved earlier.
  // Order is LIFO (Last-In, First-Out).
  popq    %rdi
  popq    %rsi
  popq    %rdx
  popq    %r10
  popq    %r8
  popq    %r9
  popq    %rcx    // RIP
  popq    %r11    // RFLAGS

  // Restore User RSP from our saved location.
  movq    scratch_rsp(%rip), %rsp

  leaq    deko_syscall_body(%rip), %rax
  movq    0(%rax), %rax

  sysretq
deko_sysret_window_end:

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
