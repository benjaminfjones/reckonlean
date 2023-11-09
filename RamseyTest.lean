import ReckonLean.Dpll
import ReckonLean.Ramsey


def tautology := dptaut

/- Prove that R(3, 3) := 6 -/
def prove_ramsey_3_3 : IO Unit :=
  let pres (s t n: Nat) : IO Unit :=
    timeit "" $ IO.println s!"s:={s}, t:={t}, n:={n}: {tautology (ramsey s t n)}"
  do
    IO.println "\nRamsey instance: prove R(3, 3) := 6\n"
    let _ <- List.mapM (pres 3 3 ·) (List.range_offset 1 6)

/-

Ramsey instance: prove R(3, 3) := 6

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

def prove_ramsey_3_4 : IO Unit :=
  let pres (s t n: Nat) : IO Unit := do
    let ramfm <- timeit s!"compute (ramsey {s} {t} {n}): " $ pure (ramsey s t n)
    let cnf <- timeit "compute defcnf_opt: " $ pure (CNF.defcnf_opt ramfm)
    let cnf_sets <- timeit "compute defcnf_opt_sets: " $ pure (CNF.defcnf_opt_sets ramfm)
    IO.println s!"number of variables: {List.length (atoms cnf)}"
    IO.println s!"number of clauses: {List.length cnf_sets}"
    timeit "tautology: " $ IO.println s!"*** s:={s}, t:={t}, n:={n}: {tautology (ramsey s t n)} *** \n"
  do
    IO.println "\nRamsey instance: prove R(3, 4) := 6\n=================================="
    let _ <- List.mapM (pres 3 4 ·) (List.range_offset 1 8)

def main : IO Unit := prove_ramsey_3_4

/-

Refuting R(3,4) := 8 is not possible in the current implementation. R(3,4) > 7 is fast
but R(3,4) > 8 overflows the stack during DP, which is not surprising. This version
is much more memory efficient than the OCmal equivalent which runs out of memory before
exhausting the stack.

Ramsey instance: prove R(3, 4) := 6
==================================
compute (ramsey 3 4 1):  4.1e-05ms
compute defcnf_opt:  0ms
compute defcnf_opt_sets:  4.1e-05ms
number of variables: 0
number of clauses: 1
tautology:  0.00171ms
*** s:=3, t:=4, n:=1: false ***

compute (ramsey 3 4 2):  4.2e-05ms
compute defcnf_opt:  0ms
compute defcnf_opt_sets:  4.2e-05ms
number of variables: 0
number of clauses: 1
tautology:  0.00162ms
*** s:=3, t:=4, n:=2: false ***

compute (ramsey 3 4 3):  4.2e-05ms
compute defcnf_opt:  4.2e-05ms
compute defcnf_opt_sets:  4.1e-05ms
number of variables: 3
number of clauses: 3
tautology:  0.00162ms
*** s:=3, t:=4, n:=3: false ***

compute (ramsey 3 4 4):  4.1e-05ms
compute defcnf_opt:  4.2e-05ms
compute defcnf_opt_sets:  4.2e-05ms
number of variables: 19
number of clauses: 40
tautology:  0.00267ms
*** s:=3, t:=4, n:=4: false ***

compute (ramsey 3 4 5):  0ms
compute defcnf_opt:  8.3e-05ms
compute defcnf_opt_sets:  4.2e-05ms
number of variables: 55
number of clauses: 136
tautology:  0.00233ms
*** s:=3, t:=4, n:=5: false ***

compute (ramsey 3 4 6):  4.2e-05ms
compute defcnf_opt:  0ms
compute defcnf_opt_sets:  4.2e-05ms
number of variables: 130
number of clauses: 346
tautology:  0.00308ms
*** s:=3, t:=4, n:=6: false ***

compute (ramsey 3 4 7):  4.2e-05ms
compute defcnf_opt:  0.000209ms
compute defcnf_opt_sets:  0.0005ms
number of variables: 266
number of clauses: 736
tautology:  0.0165ms
*** s:=3, t:=4, n:=7: false ***

compute (ramsey 3 4 8):  0.000292ms
compute defcnf_opt:  0.000583ms
compute defcnf_opt_sets:  0.000417ms
number of variables: 490
number of clauses: 1387

Stack overflow detected. Aborting.
[1]    35842 abort      build/bin/ramsey_test

-/
