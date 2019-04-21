global start
extern main
extern dsos_halt

; We claim that executing the code in this file leads to one and only one of 3
; outcomes:
;   1. the CPU halts;
;   2. the CPU raises a triple fault exception and resets;
;   3. the main() function is invoked and all of the following conditions are satisfied:
;       - The CPU supports the following features
;           - CPUID
;           - Long mode (64-bit mode)
;           - MMX
;           - SSE
;           - SSE2
;           - SSE3
;           - SSSE3
;           - SSE4.1
;           - SSE4.2
;           - POPCNT
;           - AVX
;           - AES
;           - PCLMUL
;           - FSGSBASE
;           - RDRND
;           - F16C
;           - CMPXCHG16B
;           - X87 FPU
;           - FXSR
;           - PAE
;           - 1GiB pages
;       - 64-bit mode is enabled and CS is a 64-bit read/execute code segment with DPL = 0
;       - All other segment selectors are set to the null segment
;       - Paging is enabled and the first 4 GiB of memory are identity-mapped with RWX permissions
;       - SSE and AVX are enabled
;       - 1 MiB of read-write memory is allocated for the stack
;       - The IDT is invalid so that every interrupt or exception causes a triple fault (CPU reset)
;       - The stack is 16-byte aligned before main() is invoked
;
;   We assume that:
;       - GRUB maps the entire executable in valid memory backed by RAM
;           (and not by e.g. device memory) correctly according to the ELF
;           format specification
;       - The entire software stack uses no more than 1 MiB of stack space
;       - GRUB sets up the machine according to the Multiboot2 specification:
;           - The CPU is in protected mode (PE bit set in CR0)
;           - Paging is disabled (PG bit clear in CR0)
;           - CS is a 32-bit (D flag set) read/execute code segment with an offset of 0 and a limit of 0xffffffff
;           - DS, ES, FS, GS, SS are a 32-bit (B flag set) read/write data segment with an offset of 0 and a limit of 0xffffffff
;           - The A20 gate is enabled
;           - Virtual 8086 mode is off (VM flag in EFLAGS is clear)
;           - The interrupt flag in EFLAGS is clear
;       - All device memory is inside the lowest 4 GiB of memory


section .text
BITS 32

; This is the entry point of DSOS, execution starts here
start:
    ; We must first check that the CPU features that we require are supported.
    ; Because we need to use the CPUID instruction to perform these checks, the
    ; first step we must take is to ensure that the CPU supports the CPUID
    ; instruction.
    ;
    ; The CPUID instruction is supported only if software can clear and set the
    ; ID flag (bit 21) in the EFLAGS register [Instruction set reference, CPUID].
    ;
    ; It is not possible to read or write the value of the EFLAGS register directly.
    ; Instead software must use the LAHF, SAHF, PUSHF, PUSHFD, POPF, and POPFD
    ; instructions. LAHF, SAHF, PUSHF, and POPF only operate on the lower 16 bits
    ; of the EFLAGS register, and therefore can't be used to operate on the ID
    ; flag (bit 21). Instead we have to use the PUSHFD and POPFD because they
    ; can operate on the entire EFLAGS register. PUSHFD pushes the entire EFLAGS
    ; register on the stack, and POPFD pops a 32-bit value into EFLAGS, and can
    ; change the value of the ID flag [7.3.13.2 EFLAGS Transfer Instructions].
    ;
    ; Because PUSHFD and POPFD read and write memory at the address pointed to
    ; by the stack pointer (ESP register), and pushing a 32-bit value to the stack
    ; decrements the stack pointer by 4, we must ensure that th stack pointer
    ; points to the bottom of a readable and writable region of memory at least
    ; 4 bytes in size. We instruct the assembler to allocate 1MiB of space for
    ; the stack and place the label stack_bottom at the highest address in that
    ; region. Therefore by setting esp to stack_bottom we guarantee that pushfd
    ; will not access invalid memory.
    mov esp, stack_bottom

    ; We assume that we are in protected mode with a 32-bit code segment,
    ; and that we are not in virtual-8086 mode, therefore the current
    ; operand-size attribute is 32. We assume that paging is disabled so PUSHFD
    ; cannot generate a page fault. We assume that the stack segment has a base
    ; of 0 and a limit of 0xffffffff so PUSHFD cannot cause the stack pointer
    ; to fall outside the stack segment boundary.
    ;
    ; This instruction decrements the stack pointer by 4 and writes the entire
    ; contents of EFLAGS at the address pointed to by the stack pointer.
    pushfd

    ; After executing pushfd, esp points to a valid location in memory that contains
    ; the value of the EFLAGS register. We assume that the stack segment is a
    ; 32-bit segment so the stack address size is 32-bit. The operand is a
    ; 32-bit register so the operand size is 32 bit. Therefore this instruction
    ; will read a 32-bit value from the memory adress pointed to by ESP and
    ; write it in EAX, then increment the stack pointer by 4.
    ; Because the stack segment has a base of 0 and a limit of 0xffffffff the
    ; value of ESP after this instruction cannot be outside the stack segment
    ; limit. Because paging is disabled this instruction cannot generate a page
    ; fault.
    pop eax

    ; This instruction copies ths value of the EAX register to the EBX register.
    ;
    ; This instruction does not access memory or any segment selectors or control
    ; registers, and therefore cannot cause any exceptions.
    mov ebx, eax

    ; This instruction computes the bitwise XOR between the value of
    ; the EAX register and the immediate 1 << 21. Constant expressions are
    ; evaluated by the assembler so the CPU does not execute the right shift.
    ; This will complement the value of the 21st bit of the EAX register, and
    ; all other bits will be unaffected. Because EAX contains the value of the
    ; EFLAGS register at the time PUSHFD was executed, after this instruction
    ; EAX will contain the value of the EFLAGS register at the time PUSHFD was
    ; executed with the ID flag (bit 21) complemented.
    ;
    ; This instruction does not access memory and therefore cannot cause any
    ; exceptions.
    xor eax, 1 << 21

    ; Write the new value to EFLAGS
    push eax
    popfd

    ; Read the value back. If the change has persisted then CPUID is supported
    pushfd
    pop eax

    ; If these two registers are equal CPUID is not supported
    cmp eax, ebx
    jz .unsupported_cpu


    ; --------------------------------------------------------------------------

    ; Check for SSE4.2 support. DPDK requires it starting from version 17.08
    ; https://doc.dpdk.org/guides-18.02/rel_notes/release_17_08.html

    ; Volume 1 - 12.12.3: Checking for SSE4.2 Support
    mov eax, 0x1
    cpuid

    ; All these flags must be set

    ; CPUID.01H:EDX.SSE[bit 25]
    ; CPUID.01H:EDX.SSE2[bit 26]
    mov eax, (1 << 25) | (1 << 26)
    and edx, eax
    cmp edx, eax
    jnz .unsupported_cpu

    ; CPUID.01H:ECX.SSE3[bit 0]
    ; CPUID.01H:ECX.SSSE3[bit 9]
    ; CPUID.01H:ECX.SSE4_1[bit 19]
    ; CPUID.01H:ECX.SSE4_2[bit 20]
    ; CPUID.01H:ECX.POPCNT[bit 23]
    ; CPUID.01H:ECX.XSAVE[bit 26] = 0
    mov eax, (1 << 0) | (1 << 9) | (1 << 19) | (1 << 20) | (1 << 23) | (1 << 26)
    and ecx, eax
    cmp ecx, eax
    jnz .unsupported_cpu


    ; --------------------------------------------------------------------------

    ; Check if the CPU supports 64-bit mode

    ; AMD64 Architecture Programmer's Manual, Volume 2 - 14.8: Long-Mode
    ; Initialization Example

    ; Check what is the highest CPUID extended function input that the CPU
    ; understands. If it's not at least 0x80000001, then the CPU doesn't
    ; support 64-bit mode
    mov eax, 0x80000000
    cpuid
    cmp eax, 0x80000000
    jbe .unsupported_cpu

    ; CPUID.80000001H:EDX.LM [bit 29] indicates if the processor supports 64-bit
    ; mode
    mov eax, 0x80000001
    cpuid
    bt edx, 29
    jnc .unsupported_cpu

    ; 1GB huge pages are not _really_ needed but they make our life easier
    ; CPUID.80000001H:EDX.Page1GB [bit 26]
    bt edx, 26
    jnc .unsupported_cpu


    ; --------------------------------------------------------------------------

    ; Prepare for 64-bit mode
    ;
    ; Volume 3 - 9.8.5: Initializing IA-32e Mode
    ; In order to enable 64-bit mode we first need to enable PAE and paging

    ; Enable PAE by setting bit 5 of cr4
    mov eax, cr4
    or eax, 1 << 5
    mov cr4, eax

    ; Set up the top-level page table. We could have done this statically but
    ; NASM complains...
    ;
    ; We will populate the first entry of the top-level page table (PML4) with
    ; a pointer to a 3rd level page table (PDPT)
    ; See Volume 3 - 4.2 for the structure of the page tables

    ; Pointer to the PDPT
    mov eax, pdpt
    ; Set present and writable bits for this page
    and eax, 0xFFFFF000
    or eax, 0b11
    mov [pml4], eax

    ; Load the address of the top-level page table into CR3 (we want the control
    ; bits to be 0 so we mask them off)
    mov eax, pml4
    and eax, 0xFFFFF000
    mov cr3, eax


    ; --------------------------------------------------------------------------

    ; Enable 64-bit mode - Finally the fun part!
    ; Volume 3 - 9.8.5: Initializing IA-32e Mode

    ; Setting bit 8 in MSR 0xC0000080 (IA32_EFER) tells the processor to enable
    ; 64-bit mode when we enable paging
    ;
    ; When using rdmsr/wrmsr, the number of the MSR goes in ecx and the value in
    ; edx:eax
    mov ecx, 0xC0000080
    rdmsr
    or eax, 1 << 8
    wrmsr

    ; Enable paging by setting bit 31 of cr0
    mov eax, cr0
    or eax, 1 << 31
    mov cr0, eax


    ; Volume 3 - 9.8.5.1 IA-32e Mode System Data Structures
    ; After enabling paging/64-bit mode we still need to load a 64-bit GDT.
    ; Because the CPU caches segment selectors we also need to explicitly reload
    ; the code segment by doing a far jump

    ; Load the new GDT
    lgdt [gdt64.descriptor]

    ; Far jump to the other side...
    jmp gdt64.code_segment:.64_bit


.unsupported_cpu:
    ; TODO: add an error message
    hlt
    jmp .unsupported_cpu


BITS 64

.64_bit:
    ; Welcome to 64-bit mode!
    ;
    ; 5.4.1.1 NULL Segment Checking in 64-bit Mode
    ;
    ; In 64-bit mode segment selectors can be 0, so the easiest way of getting
    ; rid of the old data segments (which have a 4GB limit) is to zero the
    ; selectors
    xor ax, ax
    mov ss, ax
    mov ds, ax
    mov es, ax
    mov fs, ax
    mov gs, ax

    ; The CPU will crash if we try to use SSE instructions unless they are
    ; initialized
    ; Volume 3 - 13.1.3: Initialization of the SSE Extensions

    ; First we need to set CR4.OSFXSR[bit 9] and CR4.OSXMMEXCPT[bit 10]
    mov rax, cr4
    or rax, (1 << 9) | (1 << 10)
    mov cr4, rax

    ; Then clear CR0.EM[bit 2] and set CR0.MP[bit 1]
    mov rax, cr0
    and rax, ~(1 << 2)
    or rax, 1 << 1
    mov cr0, rax


    ; Enable AVX: First set CR4.OSXSAVE[bit 18] to 1 (Vol. 1 - 13.3)
    mov rax, cr4
    or rax, 1 << 18
    mov cr4, rax

    ; Then set the AVX/SSE/x87 bits in XCR0
    xor rcx, rcx
    xgetbv
    or eax, 7
    xsetbv

    call main

    ; This should never be executed, but just in case...
    jmp dsos_halt



section .bss
; Stack space, statically allocated. We use stack_top to refer to the lowest
; address because the stack grows towards lower memory addresses on x86 CPUs.
; Conversely we use stack_bottom to refer to the highest memory address allocated
; to the stack.
stack_top:
    ; We guarantee 1 MiB (2^20 bytes) of stack space
    resb 1 << 20

; We guarantee that the stack pointer is aligned to 16 bytes before main() is
; invoked. Therefore we instruct the assembler to align the top of the stack
; to 16 bytes with the alignb instruction.
;
; alignb requires its first argument to be a power of 2, which we satisfy.
; alignb works with respect to the start of the current section. We instruct the
; linker to align the start of .bss to 4KiB, therefore the top of the stack is
; correctly aligned
;
; (https://www.nasm.us/doc/nasmdoc4.html#section-4.11.13)
alignb 16
stack_bottom:


; ------------------------------------------------------------------------------
section .data

; Page tables.
;
; We identity map the first 4GB (using a PML4 + 4x 1GB PDPTE
; mapping a 1GB page). 1GB is not enough because the NICs are usually mapped
; higher than that but 4GB works. Because the code is verified for memory safety
; we don't need any memory protection features and can map everything as RWX.
;
; We _could_ use 2MB pages for better compatibility but it's more tedious to set
; up and probably has a worse TLB hit rate

; Top (4th) level page table
align 4096, db 0
pml4:
    ; Nothing for now, we will fill this in at runtime
    times 512 dq 0

; 3rd level page table
align 4096, db 0
pdpt:
    ; 1GB page: present, with page size (0b1000000), writable and present bits
    ; set
    ; Physical address = 0
    dq (0x0 | 0b10000011)
    ; Same for the next 3GB
    dq (0x40000000 | 0b10000011)
    dq (0x80000000 | 0b10000011)
    dq (0xc0000000 | 0b10000011)

    ; Nothing for all other entries
    times 508 dq 0


; ------------------------------------------------------------------------------
section .rodata

; Global descriptor table for 64-bit mode
; Volume 3 - 3.5.1: Segment Descriptor Tables
gdt64:
    ; The first descriptor is never used so it can be 0
    dq 0

.code_segment: equ $ - gdt64
    ; Volume 3 - 5.2.1 Code-Segment Descriptor in 64-bit Mode

    ; Most fields are ignored in 64-bit mode so they can be 0

    ; CS.P (bit 47): descriptor present
    ; CS.S (bit 44): regular code/data (as opposed to system) segment
    ; Type (bit 43): this is a code segment
    ; CS.L (bit 53): this is a 64-bit mode code segment
    dq (1<<47) | (1<<44) | (1<<43) | (1<<53)

.descriptor:
    ; GDT descriptor
    dw $ - gdt64 - 1
    dq gdt64
