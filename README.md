# Reckonlean

This hobby project is a [Lean 4](https://github.com/leanprover/lean4) implementation
(and set of notes) for John Harrison's
[Handbook of Practical Logic and Automated Reasoning](https://doi.org/10.1017/CBO9780511576430).
This project is going on in conjunction with an internal functional programming in Lean 4
seminar following [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).

The original code accompanying Harrison's book is copyright (c) 2003-2007, John Harrison.

## Setup

Install [elan](https://github.com/leanprover/elan)

Build the project. Currently it depends on [std4](https://github.com/leanprover/std4) for some tactics, like `#guard`.

```
$ lake build
```

Run the proof and test scripts:

```
$ lake build adder_test
$ ./build/bin/adder_test
...

$ lake build ramsey_test
$ ./build/bin/ramsey_test
...
```

See `lakefile.lean` for the set of proof and test scripts defined.

## TODO

Porting from OCaml

- [x] port `formulas` (& as much of `common` as needed)
- [x] port `prop`
  - [x] port basics from `prop`
  - [x] implement `prop formula` parser as Lean syntax extension
  - [x] port basic `prop` examples
  - [x] port cnf functions
    - [x] `nnf`
    - [x] basic cnf
    - [x] implement poly finite functions with `HashMap`
    - [x] `defcnf` and `defcnf_opt`
  - [x] port enough of `prop` to support `dp`, `dpll`, and `dpli`
- [x] port adder examples
- [x] port ramsey examples