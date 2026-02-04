.text
.code64
.global _start

_start:
  // Entry point for the deko IFC component.
  // Set up the stack pointer and jump to the Rust main function.

  // Load the top of the stack into RSP.
  leaq    deko_stack_top(%rip), %rsp

  jmp     deko_ifc_entry

.data
.global deko_heap_bottom
.global deko_heap_top
.global deko_stack_bottom
.global deko_stack_top

.align 8
deko_heap_bottom:
  // Reserve 256KB (0x1000 bytes) for the deko heap.
  .fill 0x40000, 1, 0x0
deko_heap_top:
  // The heap grows upwards (from Low address to High address).

.align 8
deko_stack_bottom:
  // Reserve 64KB (0x1000 bytes) for the deko stack.
  .fill 0x10000, 1, 0x0
deko_stack_top:
  // The stack grows downwards (from High address to Low address).
