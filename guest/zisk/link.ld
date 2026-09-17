OUTPUT_ARCH(riscv)
ENTRY(_start)
PHDRS { text PT_LOAD FLAGS(1); rodata PT_LOAD FLAGS(4); data PT_LOAD FLAGS(6); }
SECTIONS {
    . = 0x80000000;
    .text.start : { KEEP(*(.text.start)) } :text
    .text.weigh : { KEEP(*(.text.weigh)) } :text
    .text : { *(.text .text.*) } :text
    .rodata : { *(.rodata .rodata.*) } :rodata
    . = 0xa0430000;
    .data : { *(.data .data.* .sdata .sdata.*) } :data
    .bss (NOLOAD) : { *(.bss .bss.* .sbss .sbss.*) *(COMMON) } :data
    _stack_top = 0xa0400000;
    /DISCARD/ : { *(.comment .note.GNU-stack .eh_frame) }
}
