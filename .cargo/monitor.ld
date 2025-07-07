OUTPUT_FORMAT("elf64-x86-64")
OUTPUT_ARCH(i386:x86-64)
ENTRY(_start)
SECTIONS
{
	. = 0x0;
	sm_entry = .;
	.text	:
	{
		*(.text .text.*)
		*(.got)
	}
	. = ALIGN(0x1000);
	.data	: 
	{ 
		*(.rodata .rodata.*)
		*(.data .data.*)
	}
	.rela	:
	{
		*(.rela .rela.* )
	}
	. = ALIGN(0x1000);
	.bss	: 
	{
		*(.bss .bss.*)
	}
	/DISCARD/	:
	{
		*(.comment*)
		*(.gnu.hash*)
		*(.hash)
	}
	sm_end = .;
	.debug	:
	{
		*(.debug .debug* )
	}
}
