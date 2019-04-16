global main
extern putchar
extern exit
BITS 64
default rel

section .text

main:
    sub rsp, 24

    rdtsc
    shl rdx, 32
    or rdx, rax
    mov rbx, rdx

.bench_loop:
    rdtsc
    shl rdx, 32
    or rdx, rax

    mov rax, rdx
    sub rax, rbx
    shr rax, 3

    cmp rax, (3500000000 >> 2)
    jbe .bench_loop

    mov rbx, rdx

    mov rdi, 0xa
    call putchar

    jmp .bench_loop

    xor rdi, rdi
    call exit

section .rodata

format_string: db `%llu\n`, 0
