/*
 * Deko's system call entry for VMPL1 applications.
 */

.equ CALLEE_SAVED_SIZE,    0x30
.equ USER_STACK_SAVE_SIZE, 0x8

.macro GS_STORE_QWORD src, offset
  movq \src, %gs:(\offset)
.endm

.macro GS_LOAD_QWORD dst, offset
  movq %gs:(\offset), \dst
.endm

/* TODO: Separate .data and .text but for now we need to
 * make sure that they are in the same page.
 */
.section .data
.global deko_trampoline_start
.global deko_trampoline_end
.global deko_ifc_engine_entry
.global deko_sysret_window_start
.global deko_sysret_window_end

deko_trampoline_start:
  // ============================================================================
  // TODO: 0. Filter out meaningless syscalls early
  // ============================================================================
  cmpq   $511, %rax
  ja     continue_analysis

  // btq    %rax, filter_bitmap(%rip)
  // jc    back_to_linux

continue_analysis:
prepare_syscall:
  swapgs

  // Save user RSP in per-CPU scratch space, then switch to the current
  // CPU's cached VMPL1 kernel stack.
  GS_STORE_QWORD %rsp, pcpu_hot + X86_user_rsp   /* 0x35c20 */
  GS_LOAD_QWORD  %rsp, pcpu_hot + X86_vmpl1_rsp  /* 0x35c28 */

  subq    $0x30, %rsp
  movq    %rbx, 0x00(%rsp)
  movq    %rbp, 0x08(%rsp)
  movq    %r12, 0x10(%rsp)
  movq    %r13, 0x18(%rsp)
  movq    %r14, 0x20(%rsp)
  movq    %r15, 0x28(%rsp)

  // Save the syscall body on the stack in DekoSyscallBody field order.
  subq    $0x50, %rsp
  movq    %rax, 0x00(%rsp)  // Syscall number
  movq    %rdi, 0x08(%rsp)  // Arg 1
  movq    %rsi, 0x10(%rsp)  // Arg 2
  movq    %rdx, 0x18(%rsp)  // Arg 3
  movq    %r10, 0x20(%rsp)  // Arg 4
  movq    %r8,  0x28(%rsp)  // Arg 5
  movq    %r9,  0x30(%rsp)  // Arg 6
  movq    %rcx, 0x38(%rsp)  // RIP
  movq    %r11, 0x40(%rsp)  // RFLAGS
  movq    %cr3, %rax
  movq    %rax, 0x48(%rsp)  // CR3

  // The syscall body is now on the stack.
call_ifc:
  movq    %rsp, %rdi
  // the pointer to the syscall body (the saved registers) is passed as the first argument to the IFC engine.
  movq    deko_ifc_engine_entry(%rip), %rax

  callq   *%rax                   // Call IFC engine

  testq   %rax, %rax
  je      return_to_user

error_hang:
  // Hang there to prevent any error from propagating to the user code.
  ud2
  hlt

return_to_user:
deko_sysret_window_start:
  // Restore the syscall body fields from the stack copy.
  movq    0x08(%rsp), %rdi
  movq    0x10(%rsp), %rsi
  movq    0x18(%rsp), %rdx
  movq    0x20(%rsp), %r10
  movq    0x28(%rsp), %r8
  movq    0x30(%rsp), %r9
  movq    0x38(%rsp), %rcx    // RIP
  movq    0x40(%rsp), %r11    // RFLAGS
  movq    0x00(%rsp), %rax

  addq    $0x50, %rsp
  movq    0x00(%rsp), %rbx
  movq    0x08(%rsp), %rbp
  movq    0x10(%rsp), %r12
  movq    0x18(%rsp), %r13
  movq    0x20(%rsp), %r14
  movq    0x28(%rsp), %r15

  addq    $0x30, %rsp

  // Restore the original rsp from the per-CPU scratch space.
  GS_LOAD_QWORD %rsp, pcpu_hot + X86_user_rsp   /* 0x35c20 */

  swapgs

  sysretq
deko_sysret_window_end:


// ============================================================================
// Data & Stack Section
// ============================================================================
// This data is embedded directly into the code page.
// We align to 8 or 16 bytes to prevent unaligned memory access penalties.

.align 8
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

deko_trampoline_end:
