import ReckonLean.Dpll
import ReckonLean.Ramsey


def tautology := dptaut

/- Prove that R(3, 3) = 6 -/
def prove_ramsey_3_3 : IO Unit :=
  let pres (s t n: Nat) : IO Unit :=
    timeit "" $ IO.println s!"s:={s}, t:={t}, n:={n}: {tautology (ramsey s t n)}"
  do
    IO.println "\nRamsey instance: prove R(3, 3) := 6\n"
    let _ <- List.mapM (pres 3 3 ·) (List.range_offset 1 6)

/-

Ramsey instance: prove R(3, 3) = 6

s:=3, t:=3, n:=1: false
 0.000583ms
s:=3, t:=3, n:=2: false
 0.0005ms
s:=3, t:=3, n:=3: false
 0.000125ms
s:=3, t:=3, n:=4: false
 0.000166ms
s:=3, t:=3, n:=5: false
 0.0015ms
s:=3, t:=3, n:=6: true
 0.00146ms

-/
-- #eval prove_ramsey_3_3

/- Prove R(3, 4) = 9 using the iterative DPLL tautology prover -/
/- instrumented verion: -/
def instrumented_prove_ramsey_3_4 : IO Unit :=
  let pres (s t n: Nat) : IO Unit := do
    let ramfm <- timeit s!"compute (ramsey {s} {t} {n}): " $ pure (ramsey s t n)
    let cnf <- timeit "compute defcnf_opt: " $ pure (CNF.defcnf_opt ramfm)
    let cnf_sets <- timeit "compute defcnf_opt_sets: " $ pure (CNF.defcnf_opt_sets ramfm)
    IO.println s!"number of variables: {List.length (atoms cnf)}"
    IO.println s!"number of clauses: {List.length cnf_sets}"
    timeit "dplbtaut: " (
      let res := dplbtaut ramfm
      IO.println s!"*** s:={s}, t:={t}, n:={n}: {res} *** \n")
  do
    IO.println "\nRamsey instance: prove R(3, 4) = 9\n=================================="
    let _ <- List.mapM (pres 3 4 ·) (List.range_offset 1 9)

def prove_ramsey_3_4 : IO Unit :=
  let prove (s t n: Nat) : Bool := dplitaut (ramsey s t n)
  do
    IO.println "\nRamsey instance: prove R(3, 4) = 9\n=================================="
    let _ <- List.mapM
      (fun n => IO.println s!"*** s:=3, t:=4, n:={n}: {(prove 3 4 n)} ***")
      (List.range_offset 1 9)

def main : IO Unit := prove_ramsey_3_4

/-
The Ramsey test formula for R(3, 4) = 9 has:

compute (ramsey 3 4 9):  0.000209ms
compute defcnf_opt:  0ms
compute defcnf_opt_sets:  0.000541ms
number of variables: 834
number of clauses: 2395

===============================================================================
`dplb`

Proving R(3, 4) = 9 with backjumping (no clause learning) DPLL prover; also slower than native DPLL

❯ time ./build/bin/ramsey_test

Ramsey instance: prove R(3, 4) = 9
==================================
*** s:=3, t:=4, n:=1: false ***
*** s:=3, t:=4, n:=2: false ***
*** s:=3, t:=4, n:=3: false ***
*** s:=3, t:=4, n:=4: false ***
*** s:=3, t:=4, n:=5: false ***
*** s:=3, t:=4, n:=6: false ***
*** s:=3, t:=4, n:=7: false ***
*** s:=3, t:=4, n:=8: false ***
*** s:=3, t:=4, n:=9: true ***
./build/bin/ramsey_test  26.12s user 0.12s system 97% cpu 26.898 total

===============================================================================
`dpli`

Proving R(3, 4) = 9 with the iterative DPLL prover; slower than naive DPLL

Ramsey instance: prove R(3, 4) = 9
==================================
*** s:=3, t:=4, n:=1: false ***
*** s:=3, t:=4, n:=2: false ***
*** s:=3, t:=4, n:=3: false ***
*** s:=3, t:=4, n:=4: false ***
*** s:=3, t:=4, n:=5: false ***
*** s:=3, t:=4, n:=6: false ***
*** s:=3, t:=4, n:=7: false ***
*** s:=3, t:=4, n:=8: false ***
*** s:=3, t:=4, n:=9: true ***
./build/bin/ramsey_test  25.31s user 0.12s system 98% cpu 25.931 total

===============================================================================
`dpll`

Proving R(3, 4) = 9 is quick with the (naive) DPLL prover!

Ramsey instance: prove R(3, 4) = 9
==================================
*** s:=3, t:=4, n:=1: false ***
*** s:=3, t:=4, n:=2: false ***
*** s:=3, t:=4, n:=3: false ***
*** s:=3, t:=4, n:=4: false ***
*** s:=3, t:=4, n:=5: false ***
*** s:=3, t:=4, n:=6: false ***
*** s:=3, t:=4, n:=7: false ***
*** s:=3, t:=4, n:=8: false ***
*** s:=3, t:=4, n:=9: true ***
build/bin/ramsey_test  9.25s user 0.06s system 96% cpu 9.644 total

===============================================================================
`dp`

Refuting R(3,4) == 8 with the DP tautology prover is not possible in the
current implementation. R(3,4) > 7 is fast but R(3,4) > 8 overflows the stack
during DP, which is not surprising. This version is much more memory efficient
than the OCmal equivalent which runs out of memory before exhausting the stack.

Time to stack blow: 7.6 seconds

Ramsey instance: prove R(3, 4) := 6
==================================
*** s:=3, t:=4, n:=1: false ***
*** s:=3, t:=4, n:=2: false ***
*** s:=3, t:=4, n:=3: false ***
*** s:=3, t:=4, n:=4: false ***
*** s:=3, t:=4, n:=5: false ***
*** s:=3, t:=4, n:=6: false ***
*** s:=3, t:=4, n:=7: false ***

Stack overflow detected. Aborting.
[1]    35842 abort      build/bin/ramsey_test
build/bin/ramsey_test  7.14s user 0.14s system 95% cpu 7.626 total

-/
