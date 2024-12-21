    opton
    call main_entry
    jmp [0x00000A18]
get_current_disk_id:
    pop rfp
    call [0x00000818]
    push r0
    jmp rfp

set_current_disk_id:
    pop rfp
    pop r0
    push rfp
    jmp [0x0000081C]

#include "main.asm"
