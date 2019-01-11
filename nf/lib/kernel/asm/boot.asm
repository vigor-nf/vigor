global start
extern dsos_halt
extern main

section .text
bits 32

start:
	; Make the processor not crash when vector instructions are used
	mov eax, cr0
	and ax, 0xFFFB
	or ax, 0x2
	mov cr0, eax
	mov eax, cr4
	or ax, 3 << 9
	mov cr4, eax

	mov esp, stack_top

	call main

	jmp dsos_halt

section .bss
align 16

stack_bottom:
	; Since there is no virtual memory, we won't notice if the stack
	; overflows and corrupts data sitting above it so make it big just in case
	;
	; 16KiB of stack was a mistake
	resb 1048576
stack_top:
