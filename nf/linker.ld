ENTRY(start)

SECTIONS {
    . = 1M;

    .boot :
    {
        /* ensure that the multiboot header is at the beginning */
        *(.multiboot_header)
    }

    .text :
    {
        *(.text)
    }

    .ctors :
    {
        __CTORS_START = .;

        *(.ctors)

    }
    __CTORS_END = .;
}
