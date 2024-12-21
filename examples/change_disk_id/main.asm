; Generated source code:
main_entry:
    sub rsp, 4
main_0:
    call get_current_disk_id
    pop r0
    mov r1, rsp
    mov [r1], r0
    mov r0, [r1]
    add r0, 1
    mov [r1], r0
    mov r0, [r1]
    push r0
    call set_current_disk_id
    add rsp, 4
    ret
