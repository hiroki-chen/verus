.text
.section ".startup.text","ax"
.code64

.globl startup_64

startup_64:
  leaq bsp_stack_end(%rip), %rsp
  xor %rbp, %rbp
  call deko_entry
  int3

.bss
.align 0x1000
.globl bsp_stack
.globl bsp_stack_end

bsp_stack:
  .fill 0x8000, 1, 0
bsp_stack_end:
