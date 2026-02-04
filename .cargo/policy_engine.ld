ENTRY(_start)

SECTIONS {
  . = 0xFFFFE90000200000; /* Base address = trampoline_va + PMD_SIZE */

  .text : {
    *(.text.entry)
    *(.text .text.*)
  }
  .rodata : {
      *(.rodata .rodata.*)
  }

  .data : {
      *(.data .data.*)
  }

  .bss : {
      *(.bss .bss.*)
  }

  /DISCARD/ : {
      *(.comment)
      *(.eh_frame)
  }
}
