; Generated source code:
main:
    pop rfp
    pop r0
    push rfp
    sub rsp, 4
main_0:
    mov r1, rsp
    mov [r1], r0
    mov r0, [r1]
    push r1
    push 72
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 101
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 108
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 108
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 111
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 44
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 32
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 119
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 111
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 114
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 108
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 100
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push r1
    push 33
    push r0
    call print_char
    pop r1
    mov r0, [r1]
    push 10
    push r0
    call print_char
    add rsp, 4
    ret

print_char:
    pop rfp
    pop r0
    pop r2
    push rfp
    sub rsp, 12
print_char_0:
    mov r1, rsp
    mov [r1], r0
    mov r0, rsp
    add r0, 4
    mov [r0], r2
    push r1
    push r0
    push 4
    call allocate_memory
    pop r2
    pop r0
    pop r1
    mov r3, rsp
    add r3, 8
    mov [r3], r2
    mov r2, [r3]
    mov r0, [r0]
    mov [r2], r0
    mov r0, [r1]
    mov r1, [r3]
    push r3
    push r1
    push r0
    push 1
    call write
    pop r3
    mov r0, [r3]
    push r0
    call free_memory
    add rsp, 12
    ret
