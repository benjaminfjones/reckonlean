# Reckonlean

This hobby project is a [Lean 4](https://github.com/leanprover/lean4) implementation
(and set of notes) for John Harrison's
[Handbook of Practical Logic and Automated Reasoning](https://doi.org/10.1017/CBO9780511576430).
This project is going on in conjunction with an internal functional programming in Lean 4
seminar following [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).

Currently, I'm working on porting [reckoning](https://github.com/benjaminfjones/reckoning), which was a (partial) modern OCaml adaptation of Harrison's code.

The original code accompanying Harrison's book is copyright (c) 2003-2007, John Harrison.

## TODO

- [x] port `formulas` (& as much of `common` as needed)
- [-] port `prop`
  - [x] port basics from `prop`
  - [x] implement `prop formula` parser as Lean syntax extension
  - [ ] port basic `prop` examples
  - [ ] port `nnf` and `defcnf`
  - [ ] port enough of `prop` to support `dp`, `dpll`, and `dpli`
- [ ] port adder examples
- [ ] port ramsey examples

- [ ] ...
