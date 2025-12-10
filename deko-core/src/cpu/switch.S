.equ  RSP_OFFSET, 0  // 16 registers pushed onto stack

.text

.globl context_switch

context_switch:
  // void_t context_switch(uint64_t pre, uint64_t next)
  // Save the current context (pre) and switch to the next context (next)
  pushfq // offset = 0 with flags.
  pushq %rax
  pushq %rbx
  pushq %rcx
  pushq %rdx
  pushq %rsi
  pushq %rdi
  pushq %rbp
  pushq %r8
  pushq %r9
  pushq %r10
  pushq %r11
  pushq %r12
  pushq %r13
  pushq %r14
  pushq %r15
  pushq %rsp 

  testq   %r12, %r12   // pre == null
  je    1f         

  movq    %rsp, RSP_OFFSET(%r12)  # save current rsp into pre->rsp
  mov     %r14, %rsp

1:
  mov    %r15, %cr3 // load new page table

.done:
  movq   RSP_OFFSET(%r13), %rsp  # load next rsp
  addq   $8, %rsp   # skip saved rsp

  popq    %r15

  hlt 
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
