# Olea's bad calling convention

## Caller

all live general registers and `rfp` are pushed by the callee. Arguments are pushed on the stack, last argument pushed first, followed by the code address to return to (handled implicitly by the `call` instruction). Return values are popped to the stack, first value popped first. Saved registers are then popped.

## Callee

The top value (return code address) is popped to `rfp`. The parameters are on the stack, first parameter first. Execution returns to the caller by moving the stack pointer to the saved registers, pushing the return values, last value pushed first, and jumping to the address in `rfp`.
