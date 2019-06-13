section .multiboot_header

header_start:
    dd 0x1BADB002        ; magic number (multiboot 1)
    dd 3                 ; multiboot flags
    dd -(0x1BADB002 + 3) ; header checksum

header_end:
