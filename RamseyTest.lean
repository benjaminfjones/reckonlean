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

/- Prove R(3, 4) = 9 using the DPLL tautology prover -/
def prove_ramsey_3_4 : IO Unit :=
  let pres (s t n: Nat) : IO Unit := do
    let ramfm <- timeit s!"compute (ramsey {s} {t} {n}): " $ pure (ramsey s t n)
    let cnf <- timeit "compute defcnf_opt: " $ pure (CNF.defcnf_opt ramfm)
    let cnf_sets <- timeit "compute defcnf_opt_sets: " $ pure (CNF.defcnf_opt_sets ramfm)
    IO.println s!"number of variables: {List.length (atoms cnf)}"
    IO.println s!"number of clauses: {List.length cnf_sets}"
    timeit "dplltaut: " (
      let res := dplltaut ramfm
      IO.println s!"*** s:={s}, t:={t}, n:={n}: {res} *** \n")
  do
    IO.println "\nRamsey instance: prove R(3, 4) = 9\n=================================="
    let _ <- List.mapM (pres 3 4 ·) (List.range_offset 1 9)

def main : IO Unit := prove_ramsey_3_4

/-

Proving R(3, 4) = 9 is quick with the (naive) DPLL prover!

Ramsey instance: prove R(3, 4) = 9
==================================
compute (ramsey 3 4 1):  8.4e-05ms
compute defcnf_opt:  4.1e-05ms
compute defcnf_opt_sets:  0ms
number of variables: 0
number of clauses: 1
dplltaut:  0.00196ms
*** s:=3, t:=4, n:=1: false ***

compute (ramsey 3 4 2):  4.2e-05ms
compute defcnf_opt:  0ms
compute defcnf_opt_sets:  4.1e-05ms
number of variables: 0
number of clauses: 1
dplltaut:  0.00154ms
*** s:=3, t:=4, n:=2: false ***

compute (ramsey 3 4 3):  4.2e-05ms
compute defcnf_opt:  4.1e-05ms
compute defcnf_opt_sets:  4.2e-05ms
number of variables: 3
number of clauses: 3
dplltaut:  0.00171ms
*** s:=3, t:=4, n:=3: false ***

compute (ramsey 3 4 4):  4.2e-05ms
compute defcnf_opt:  4.2e-05ms
compute defcnf_opt_sets:  0.000167ms
number of variables: 19
number of clauses: 40
dplltaut:  0.00358ms
*** s:=3, t:=4, n:=4: false ***

compute (ramsey 3 4 5):  4.2e-05ms
compute defcnf_opt:  4.2e-05ms
compute defcnf_opt_sets:  4.1e-05ms
number of variables: 55
number of clauses: 136
dplltaut:  0.00208ms
*** s:=3, t:=4, n:=5: false ***

compute (ramsey 3 4 6):  4.1e-05ms
compute defcnf_opt:  4.2e-05ms
compute defcnf_opt_sets:  0ms
number of variables: 130
number of clauses: 346
dplltaut:  0.0025ms
*** s:=3, t:=4, n:=6: false ***

compute (ramsey 3 4 7):  4.2e-05ms
compute defcnf_opt:  4.1e-05ms
compute defcnf_opt_sets:  0.000667ms
number of variables: 266
number of clauses: 736
dplltaut:  0.00654ms
*** s:=3, t:=4, n:=7: false ***

compute (ramsey 3 4 8):  4.1e-05ms
compute defcnf_opt:  0.000334ms
compute defcnf_opt_sets:  0.000833ms
number of variables: 490
number of clauses: 1387
dplltaut:  0.00896ms
*** s:=3, t:=4, n:=8: false ***

compute (ramsey 3 4 9):  4.2e-05ms
compute defcnf_opt:  0.00025ms
compute defcnf_opt_sets:  0ms
number of variables: 834
number of clauses: 2395
dplltaut:  0.0127ms
*** s:=3, t:=4, n:=9: true ***

build/bin/ramsey_test  9.25s user 0.06s system 96% cpu 9.644 total

Refuting R(3,4) == 8 with the DP tautology prover is not possible in the
current implementation. R(3,4) > 7 is fast but R(3,4) > 8 overflows the stack
during DP, which is not surprising. This version is much more memory efficient
than the OCmal equivalent which runs out of memory before exhausting the stack.

Time to stack blow: 7.6 seconds

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
build/bin/ramsey_test  7.14s user 0.14s system 95% cpu 7.626 total

-/
