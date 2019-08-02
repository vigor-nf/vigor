ENTRY(start)

SECTIONS
{
    . = 1M;

    .boot ALIGN(4K) :
    {
        *(.multiboot_header)
    }

    .text ALIGN(4K) :
    {
        *(.text)

        KEEP(*(.init))
        KEEP(*(.fini))

        /* .ctors */
        *crtbegin.o(.ctors)
        *crtbegin?.o(.ctors)
        *(EXCLUDE_FILE(*crtend?.o *crtend.o) .ctors)
        *(SORT(.ctors.*))
        *(.ctors)

        /* .dtors */
        *crtbegin.o(.dtors)
        *crtbegin?.o(.dtors)
        *(EXCLUDE_FILE(*crtend?.o *crtend.o) .dtors)
        *(SORT(.dtors.*))
        *(.dtors)
    }

    .data ALIGN(4K) :
    {
        *(.data)
    }

    .rodata ALIGN(4K) :
    {
        *(.rodata)
    }

    .bss ALIGN(4K) :
    {
        *(.bss)
    }
}
