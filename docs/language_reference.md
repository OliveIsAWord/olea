# Olea Language Reference

This document is an informal overview of the Olea programming language. It documents all syntactic constructs and the broad semantics of Olea programs.

## Syntax Fundamentals

Olea uses an "indentation-based" syntax, meaning that line breaks and the whitespace at the start of each line have semantic meaning to the program. In the current Olea compiler, this is all done as an additional stage between lexing and parsing known as "arborization". (Aside from comments, which are handled in the lexer stage)

### Comments

"Line comments" start with a hash (`#`) and continue until the next line break.

```
some code # a comment
more code
```

### Blocks

A block is a list of items separated by line breaks. Declarations and statements are both items. An Olea program is just a block.

```
item 1
item 2
item 3
```

An indented region following an item continues that item.

```
item 1
    something else in item 1
    yet another thing in item 1
item 2
item 3
```

A colon (`:`) followed by a line break and an indented region starts a new block.

```
item 1:
    sub item 1
    sub item 2
```

If the colon is not followed by a line break, it starts a new block of just 1 item.

```
item 1: sub item 1
item 2: sub item 2
```

### Brackets

Brackets in Olea are a matching pair of parentheses or square brackets, containing a list of items. These items are separated by commas or line breaks.

```
foo(a, b, c)
bar[x, y,] # A trailing comma is allowed

foo(
    a
    b
    c
)
bar[
    x
    y
]
```

Commas can terminate a block within brackets.

```
(item 1: sub item 1, item 2: sub item 2)
```

In some cases, the grammar distinguishes between a "single" item in brackets, which has one item and no trailing comma, and a "list" of items in brackets, which has zero or multiple items or is a single item with a trailing comma.  (For example, a parenthesized expression vs. a tuple of one element)

```
(a) # this item
(a,) # may be parsed differently than this item
```

### `else` Item

An item starting with the `else` keyword continues the previous item.
```
item 1
else this is still item 1
item 2
```

## Syntax Used in This Document

Angle brackets indicate a required section. Curly brackets indicate an optional section. An ellipsis (`...`) at the end of an item indicates the item may appear zero or more times, separated by either line breaks or commas. An ellipsis *after* an item indicates that item may appear one or more times, separated by either line breaks or commas.

## Types

### Names

```rs
<type name>
```

Structs and built-in types are accessed by name. The built-in types include the integers (`u8`, `u16`, `u32`, and `usize`) and the boolean type `bool`.

### Pointers

```rs
<type>^
```

A pointer is a value that can be used to access a region of memory.

### Function Pointers

```rs
fn({anon} <parameter name>: <type>...) {type}
```

A function pointer can be called with the appropriate parameters via function call or method call.

### Arrays

```rs
<type>[<constant expression>]
```

An array is a contiguous list of fixed length.

## Declarations

An Olea program is a list of declarations.

### Functions

```rs
fn <function name>({anon} <parameter name>: <parameter type>...) {return type}:
    <statement>
    ...
```

A function is a named body of code that can be entered and exited. The `anon` keyword indicates whether the parameter can be passed anonymously (see [function calls](#function-calls)). If the return type is specified, the last statement must be an expression whose value is yielded.

### Extern Functions

```rs
extern fn <function name>({anon} <parameter name>: <parameter type>...) {return type}
```

An `extern` function is syntactically the same as a normal function, besides starting with the `extern` keyword and not having a body block, and can be called exactly like a normal function. An `extern` function's code must be provided at the linking stage (i.e. after compilation).

### Structs

```rs
struct <struct name>:
    {anon} <field name>: <field type>
    ...
```

It's also possible to define a struct with no fields:

```rs
struct <struct name>
```

A struct declaration defines a named type whose values are composed of zero or more named field values. It also defines a "constructor" function with the same name as the struct which accepts the fields as parameters and returns the constructed struct value. The `anon` keyword indicates whether the parameter of the constructor function can be passed anonymously (see [function calls](#function-calls)).

### Statements

A function block or block expression is a list of statements.

### Expression Statements

```rs
<expression>
```

An expression statement evaluates its expression, either discarding or yielding its value depending on if it's the tail expression of a block that must yield a value.

### `let` Bindings

```rs
let <name> {type} = <expression>
```

Creates a local variable that can be accessed by name and by pointer in expressions. Olea is "lexically scoped", meaning this variable can be accessed in any following statements of the block this `let` binding appears in. Olea also allows local variables to "shadow" outer items of the same name, meaning the latter is no longer accessible for the lifetime of the variable. The lifetime of the variable's memory region is the same as the variable's scope (shadowing does not affect this).

### Assignments

```rs
<place expression> = <expression>
```

Write a value to a location in memory that the [place expression](#place-expressions) refers to. Most commonly this is used to mutate local variables.

### `return`, `continue` and `break`

TODO: Not yet implemented.

```rs
return {expression}
continue
break {expression}
```

A `return` statement exits the current function, yielding the value of its expression if present. If the function has a return type, the return statement must have an expression that matches this type.

A `continue` statement jumps to the condition expression of the inner-most `while` loop.

A `break` statement exits the inner-most `while` loop, yielding the value of its expression if present.

### `defer`

TODO: Not yet implemented.

```rs
defer {expression}
```

A `defer` statement declares an expression that will be evaluated when control flow exits from the current block.

## Expressions

### Precedence

Operations in the same row have equal precedence, and higher precedence (a stronger binding power) than operations in the rows below them.

Operator Category | Operators | Associativity
--- | --- | ---
Postfix | `^`, `@`, `as`, function calls, array indexing, field access, method calls |  Left-to-right
Prefix | negation `-` | Right-to-left
Multiplication | `*`, `/` | Left-to-right
Addition | `+`, subtraction `-` | Left-to-right
Comparison | `==`, `!=`, `<`, `>`, `<=`, `>=` | See [comparison operators](#comparison-operators)
And | `and` | Left-to-right
Or | `or` | Left-to-right

Evaluating contrary to these precedence levels requires placing sub-expressions within parentheses.

<!-- This lets us have associativity span multiple rows, but manually specifying <code> for each operator is tiring.
<table>
    <thead>
        <tr>
            <th>Operator Category</th>
            <th>Operators</th>
            <th>Associativity</th>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td>Postfix</td>
            <td>`^`, `@`, function calls, array indexing, field access, method calls</td>
            <td>Left-to-right</td>
        </tr>
        <tr>
            <td>Prefix</td>
            <td>negation `-`</td>
            <td>Right-to-left</td>
        </tr>
        <tr>
            <td>Multiplication</td>
            <td>`*`, `/`</td>
            <td rowspan=2>Left-to-right</td>
        </tr>
        <tr>
            <td>Addition</td>
            <td>`+`, subtraction `-`</td>
        </tr>
    </tbody>
</table>
-->

### Place Expressions

A "place expression" is an expression that is associated with the memory region in which its value is stored. This includes [variables](#variables), [dereferences](#dereferences), [array indexing](#array-indexing), and [field accesses](#field-accesses). Certain expressions and statements require that, or behave differently if, a certain expression is a place expression.

### Integers

```
<digits>{suffix}
```

A decimal integer value. The suffix must be the name of an integer type, which determines the type of the integer. If no suffix is specified, the integer is of type `usize`.

### Strings

```rs
"<character>..."
```

A `u8` pointer to static memory containing the null-terminated, UTF-8 encoded character data of the string. Supports certain escape characters. A string can only span one line.

### Variables

```rs
<name>
```

The value of a local or global variable.

### Tuples

TODO: Not yet implemented.

```rs
(<function argument>...)
```

Tuples are "anonymous" struct values. See [future language direction](#future-language-direction).

### Block Expressions
```rs
:
    <statement>
    ...
```

A block expression evaluates its statements in order and, if the last statement is an expression (known as a "tail expression"), yields the value of that expression. Block expressions are useful for constraining the bounds of a `let` or `defer` statement, or as the expression of an `else` branch or `defer` statement.

### Arithmetic Operators

```rs
<expression> + <expression>
<expression> - <expression>
<expression> * <expression>
<expression> / <expression>
- <expression>
```

These operations perform addition, subtraction, multiplication, division, and negation respectively. Both expressions must be integers (no pointer arithmetic!). Currently, all integers are treated as two's complement unsigned integers.

### Comparison Operators

```rs
<expression> == <expression>
<expression> != <expression>
<expression> < <expression>
<expression> > <expression>
<expression> <= <expression>
<expression> >= <expression>
```

Tests for equality, inequality, or ordering between two values. Yields `true` if the comparison holds, `false` otherwise.

Comparisons can be "chained". E.g. `x < y < z` is equivalent to `x < y and y < z` except that the expression `y` is only evaluated once. Such a chain must be "well formed", meaning that all the comparison operators must have a consistent ordering direction. This definition will be changed or refined in the future.

### Boolean Operators

```rs
<expression> and <expression>
<expression> or <expression>
```

The `and` and `or` operators combine two boolean values into one, by logical conjunction and disjunction respectively. These operators are "lazy" or "short-circuiting", meaning that the right hand subexpression does not execute if its value cannot affect the result. More precisely, if the left operand of an `and` expression yields `false` or the left operand of an `or` operation yields `true`, the right operand is not evaluated.

### `as` Casting

```rs
<expression> as <integer type>
<expression> as <pointer type>
```

Convert a value to a different type. With an integer cast, the integer value will be converted to the given type, wrapping and truncating to fit its bounds as appropriate. With a pointer cast, the inner type of the pointer value can be arbitrarily changed.

### Function Calls

```rs
<expression>(<function argument>...)
```

Where a function argument is any of the following:

```rs
<name>: <statement>... # "named" argument
: <statement>... # "punned" or "name punned" argument
<expression> # "anonymous" or "positional" argument
```

In Olea, unless the corresponding parameter is marked as `anon`, all function arguments must be explicitly named for a function call. If the parameter is `anon`, its argument can be passed positionally. The function arguments are evaluated in order. The position of named arguments does not otherwise matter.

Name punning allows eliding the explicit name of a named argument, if the tail expression of the argument "puns" to that name. Variable expressions pun to the variable name, and field access expressions pun to the field name. More expressions may be able to pun in the future.

### Method Calls

TODO: Not yet implemented. Also, the semantics described are subject to change.

```rs
<expression>.<function name>(<function argument>...)
```

Olea supports [Uniform Function Call Syntax](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax), allowing functions to be called with the "receiver" expression passed as the argument corresponding to the first parameter.

### References

```rs
<expression>@
```

Yields a pointer to the value of the expression. If referencing a place expression, this will be the pointer to its associated memory region. Otherwise, it will be a pointer to a temporary allocation that lives for the duration of the current statement.

### Dereferences

```rs
<expression>^
```

Yields the value that a pointer refers to.

### Array Indexing

TODO: Currently, indexing can only be done through a pointer.

```rs
<expression>[<expression>]
```

### Field Accesses

TODO: Currently, field access can only be done through a pointer.

```rs
<expression>.<field name>
```

Yields the value of the field of the struct value.

### `if` Expressions

```rs
if <condition expression>:
    <statement>
    ...
{ else <expression> }
```

An `if` expression evaluates its boolean condition, executing its body if `true`. If the `else` branch is present, that expression is executed if the condition is `false`. The types of the values yielded by the two branches only need to match if the surrounding context of the `if` expression requires it to yield a value.

### `while` Loops

TODO: `else` branch

```rs
while <condition expression>:
    <statement>
    ...
{ else <expression> }
```

A `while` loop repeatedly evaluates its condition and body in an alternating pattern until the condition is `false`, or until a `break` statement terminates the loop. If the condition yields `false`, the else branch is evaluated and yielded.

## Future Language Direction

The following passages provide insight into the ways the Olea language may evolve, beyond the TODOs already listed, both short- and long-term.

- Plenty of Rust features that we are missing: enums and pattern matching, traits, generics, constant evaluation, etc.

- One theme of the language is the unification of structs, tuples, and function arguments (and maybe enums too!). For example, in the future, you might be able to call functions like so:

```rs
fn foo(a: usize, anon b: str^): ...
let args = (a: 42, "Hello, world!")
args |> foo
```

We might even provide mutually exclusive parameters to correspond with enums:

```rs
fn either_or(a_or_b: (a: u32 | b: u16)):
    match a_or_b:
        (:a) => println!("got a: {a}")
        (:b) => println!("got b: {b}")

either_or(a: 42)
either_or(b: 65000)
either_or(a: 42, b: 65000) # error
```

- The status quo for the order of evaluation in expressions has not sat right with me. We can imagine two broad approaches. One is the approach C takes, where evaluation order is unspecified save for a few exceptions like logical AND and OR and the comma operator. The other is the approach Rust takes, where evaluation order is fully specified as left to right (?).

The Rust approach leads to more consistency when running code across implementations or versions of compilers, but requires more complicated or even infeasible analysis to reorder evaluation for optimization purposes. Both approaches do not clarify whether a piece of code depends on a certain order of evaluation. There must be a better way!

What if expressions allowed at most one "impure" subexpression? That would mean any evaluation order would produce the same observable result! It also means the sequence of impure operations must be explicitly ordered by the programmer in terms of a sequence of statements. e.g. instead of writing...

```rs
impure1() + impure2()
```

... you would have to write...

```rs
let x = impure1()
x + impure2()
```

To explicitly leave evaluation order unspecified, for operations whose side effects are mutually exclusive or otherwise do not change the behavior or correctness of the program, we might bless a specific syntax:

```rs
let:
    x = impure1()
    y = impure2()
x + y
```

We might have an `impure` keyword that marks functions with side effects and variables whose body has side effects in this let block syntax.

This approach may be incompatible or less ergonomic with other language features like borrow checking. Evaluation order obviously matters a lot when determining when borrows live and die, so this approach might require things like mutable borrows to be considered impure.

- A dedicated syntax for the `Option` type and optional arguments.

```rs
# these two functions have compatible function signatures
fn foo(required: T?, ?optional: T): ... # in the function body, `optional` has type `T?`
fn with_default(required: T?, ?optional: T = T::Connected): ... # in the function body, `optional` has type `T`
foo(required: Some(t))
foo(required: None, optional: T::Severed)
foo(required: None, ?optional: Some(T::Tenuous)) # explicitly pass by option, useful for chaining optional parameters
```

- Field access and method calling without a receiver (e.g. `.field` or `.method()`) that implicitly uses the first argument of the function as the receiver.

- Compile-time evaluation and metaprogramming, including being able to reify types and syntactic elements as values. The syntax for structs and functions may radically change.

- Signed integer types.

- Range-based integer types that precisely specify the range of possible integer values, rather than just the bit width. The existing integer types would just be aliases for their equivalent ranges.

- Multi-dimensional array indexing?

- Allow declarations as statements.
