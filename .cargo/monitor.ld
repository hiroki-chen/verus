/*
 * Kernel Linker Script for x86-64
 * Loads the kernel at physical address 2 MiB
 */
ENTRY(_start)
OUTPUT_FORMAT(elf64-x86-64)

PHDRS
{
    text PT_LOAD FLAGS(5); /* R+X */
    rodata PT_LOAD FLAGS(4); /* R */
    data PT_LOAD FLAGS(6); /* R+W */
}

SECTIONS
{
    /* This is the most important line! */
    /* It sets the location counter to 2 MiB. */
    . = 0x200000;

    .text : ALIGN(4K) {
        KEEP(*(.text.entry)) /* Keep the entry point at the very start */
        *(.text .text.*)
    } :text

    .rodata : ALIGN(4K) {
        *(.rodata .rodata.*)
    } :rodata

    .data : ALIGN(4K) {
        *(.data .data.*)
    } :data

    .bss : ALIGN(4K) {
        *(.bss .bss.*)
        *(COMMON)
    } :data

    /DISCARD/ : {
        *(.comment)
        *(.note*)
    }
}
