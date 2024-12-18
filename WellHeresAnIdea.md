So this code has gone stagnant and grown mold while I was dreading implementing a register allocator I could live with! What remains in this commit are the dead soldiers of my multiple efforts. Described here is my *next* attempt; this time will surely be the one. Like the rest of codegen (and the rest of this project, frankly), this register allocator does not need to be very good. It just needs to be easy and correct (at least as best as we can manage, just like the rest of this project). Notably, efficiency is *not* a priority until it grows untenable (e.g. when we're finally building programs large enough to expose the various internal algorithms with unacceptable time complexity).

- Take our liveness data and construct an interference graph.
- Pre-color StackAlloc and maybe function arguments too?
- Optional: Construct a "soft" graph of IR registers that ought to be allocated the same register if possible (e.g. phi arguments, lhs alu arguments).
- Do a basic greedy graph coloring.

```
while let x = unassigned IR register:
    let reg = the best unused register (e.g. start at r0, go up to r30 and then try stack allocation)
    assign x to reg
    let live = {x}
    // optional
    while let y = unassigned IR register in soft.get(x) that does not interfere with any register in live:
        assign y to reg
        live.insert(y)
    while let y = unassigned IR register that does not interfere with any register in live:
        assign y to reg
        live.insert(y)
```

I think I can actually implement this! Wish me luck :3
