global start
extern main
extern dsos_halt
extern printf
extern mystery2
extern dsos_vga_write_char

; This is the bootstrap code of DSOS. At a high level it does the following:
;
;   - Checks that the CPU supports the features we need
;   - Enables paging and identity maps the first 4GB of memory
;   - Switches to 64-bit mode
;   - Enables SSE support
;
; After initialization it jumps to the C main function which should never
; return
;
; All references to book chapters are to the Intel x86 manual unless otherwise
; noted

section .text

BITS 32
; This is the entry point of DSOS. The bootloader will jump here when it's done
start:

    ; DSOS does not handle interrupts so disable them
    cli

    ; Initialize the stack (needed for pushfd/popfd)
    mov esp, stack_top

    ; Volume 1 - 19.1: Using the CPUID instruction
    ; If we can set and clear the ID bit in EFLAGS (bit 21) then CPUID is
    ; supported. We want to use CPUID to check for other features so this is
    ; required

    ; Read the value of eflags
    pushfd
    pop eax

    ; Keep the old value around to compare later
    mov ebx, eax
    ; Toggle the value of the ID bit (bit 21)
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

; Stack space, statically allocated
alignb 16
stack_bottom:
    ; Since there is no virtual memory, we won't notice if the stack
    ; overflows and corrupts data sitting above it so make it big just in case
    ;
    ; 16KiB of stack was a mistake
    resb 1048576
stack_top:


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

format_string: db `%lu\n`, 0

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
