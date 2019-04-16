global main
extern printf
extern exit
BITS 64
DEFAULT rel

section .text

main:
	sub rsp, 8
	rdtsc
    shl rdx, 32
    or rax, rdx
    mov r8, rax

    mov rcx, 1 << 34

.bench_loop:
    mov rbx, [test]
    mov [test], rbx
    dec rcx
    jnz .bench_loop

    rdtsc
    shl rdx, 32
    or rax, rdx

    sub rax, r8
    lea rdi, [test_fmt]
    mov rsi, rax
    call printf

	xor rdi, rdi
	call exit

section .data

test: dq 0

section .rodata

test_fmt: db `%lu\n`, 0
