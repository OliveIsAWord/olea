    opton
    call main
    jmp [0x00000A18] ; end_current_task

write:
    pop rfp
    pop r0
    pop r1
    pop r2
    push rfp
    jmp [0x00000D20]

#include "main.asm"
