    opton
    call main
    jmp [0x00000A18]

allocate_memory:
    pop rfp
    pop r0
    call [0x00000B10]
    push r0
    jmp rfp

free_memory:
    pop rfp
    pop r0
    call [0x00000B14]
    jmp rfp

write:
    pop rfp
    pop r0
    pop r1
    pop r2
    push rfp
    jmp [0x00000D20]

#include "main.asm"
