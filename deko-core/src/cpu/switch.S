.equ  RSP_OFFSET, 0
.text

.globl context_switch

context_switch:
  // void_t context_switch(uint64_t pre, uint64_t next)
  // Save the current context (pre) and switch to the next context (next)
  pushfq // offset = 0 with flags.
  pushq   %rax
  pushq   %rbx
  pushq   %rcx
  pushq   %rdx
  pushq   %rsi
  pushq   %rdi
  pushq   %rbp
  pushq   %r8
  pushq   %r9
  pushq   %r10
  pushq   %r11
  pushq   %r12
  pushq   %r13
  pushq   %r14
  pushq   %r15
  pushq   %rsp 

  testq   %r12, %r12   // pre == null
  jz      1f

  // Problematic: ...
  movq    %r12, %rax
  addq    %r11, %rax   // pre + offset_of(rsp)
  movq    %rsp, (%rax)  # save current rsp into pre->rsp
  mov     %r14, %rsp

1:
  mov    %r15, %cr3 // load new page table

2:
  // Be extra careful with the stack pointer here as we cannot directly load
  // RSP from SOME_OFFSET(%r13) since we don't make `DekoRunnable` repr(C) and
  // thus we cannot assume that task.rsp is at the beginning of the struct.
  //
  // Instead, we pass the next rsp in r11 register from Rust side so that we can
  // directly load it here and recover the context (which is repr(C)) directly.

  movq    %r13, %rax
  addq    %r11, %rax   // next + offset_of(rsp)
  movq    (%rax), %rsp  # load next rsp from next->rsp
  addq    $8, %rsp   # skip saved rsp

  popq    %r15
  popq    %r14
  popq    %r13
  popq    %r12
  popq    %r11
  popq    %r10
  popq    %r9
  popq    %r8
  popq    %rbp
  popq    %rdi
  popq    %rsi
  popq    %rdx
  popq    %rcx
  popq    %rbx
  popq    %rax
  popfq

  retq
