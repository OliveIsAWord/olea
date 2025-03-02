    opton
    call main
    jmp [0x00000A18] ; end_current_task

allocate_memory:
    pop rfp
    pop r0
    call [0x00000B10]
    push r0
    jmp rfp

free_memory:
    pop rfp
    pop r0
    push rfp
    jmp [0x00000B14]

new_window:
    pop rfp
    pop r0
    pop r1
    pop r2
    pop r3
    pop r4
    pop r5
    pop r6
    pop r7
    push rfp
    jmp [0x00000C10]

destroy_window:
    pop rfp
    pop r0
    push rfp
    jmp [0x00000C14]

get_next_window_event:
    pop rfp
    pop r0
    call [0x00000C1C]
    push r7
    push r6
    push r5
    push r4
    push r3
    push r2
    push r1
    push r0
    jmp rfp

get_window_overlay_number:
    pop rfp
    pop r0
    call [0x00000C2C]
    push r0
    jmp rfp

start_dragging_window:
    pop rfp
    pop r0
    call [0x00000C30]
    jmp rfp

draw_str_to_overlay:
    pop rfp
    pop r0
    pop r1
    pop r2
    pop r3
    pop r4
    pop r5
    push rfp
    jmp [0xF0043004]

yield_task:
    jmp [0x00000A14]

breakpoint:
    brk
    ret

#include "main.asm"
