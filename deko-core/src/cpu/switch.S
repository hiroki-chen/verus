.equ  RSP_OFFSET 8*16  // 16 registers pushed onto stack
.equ  SSP_OFFSET RSP_OFFSET + 8 // RSP saved after registers


.text

.global context_switch

.context_switch:
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

  test %rdi, %rdi   # if (next == 0)
  je .done          #   goto done


.done:
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
