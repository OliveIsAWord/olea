# Asterid Notation

Asterid notation is a lexing convention that implements a form of whitespace sensitive grammar. Asterid is inspired by Python's grammar, Rust's style guide, and Shrubbery notation (a project with very similar goals to ours).

## Principles

- The grammar should, where possible, accept the shapes recommended by Rust style conventions.

- The grammar should handle tab characters without presupposing how long a tab is. This means **no aligning** except for the starts of lines!

## Grammar

```ebnf
program := block

block := expr*

expr := (tokens | '(' block ')')* (':' block else_block?)?

else_block := 'else' (':' block | expr)
```
