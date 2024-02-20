import ReckonLean.Adder
import ReckonLean.Dpll

/-
Formula representing the equivalence of carryselect n k and ripplecarry n
-/
def mk_carryselect_ripple_equivalence (n k: Nat) : PFormula :=
  -- define all the bitvectors
  let x := mk_bit "x"
  let y := mk_bit "y"
  let c := mk_bit "c"
  let s := mk_bit "s"
  let c0 := mk_bit "c0"
  let s0 := mk_bit "s0"
  let c1 := mk_bit "c1"
  let s1 := mk_bit "s1"
  let c2 := mk_bit "c2"
  let s2 := mk_bit "s2"
  Formula.Imp
    -- carry select with 0 carry relation AND ripplecarry relation over same inputs
    (.And
        (.And (carryselect n k x y c0 c1 s0 s1 c s) (.Not (c 0)))
        (ripplecarry0 n x y c2 s2 )
    )
    -- carry outputs and sum outputs are equivalent
    (.And
      (.Iff (c n) (c2 n))
      (conjoin (fun i => .Iff (s i) (s2 i)) (List.range n))
    )

def ex_4_2 := mk_carryselect_ripple_equivalence 4 2
-- 39 variables
#guard List.length (atoms ex_4_2) == 39
-- 407 clauses
#guard List.length (CNF.defcnf_opt_sets ex_4_2) == 407
-- 427 clauses for the equivalence proof
#guard List.length (CNF.defcnf_opt_sets (.Not ex_4_2)) == 427

def ex_5_3 := mk_carryselect_ripple_equivalence 5 3
-- 48 variables
#guard List.length (atoms ex_5_3) == 48
-- 498 clauses
#guard List.length (CNF.defcnf_opt_sets ex_5_3) == 498
-- 521 clauses for the equivalence proof
#guard List.length (CNF.defcnf_opt_sets (.Not ex_5_3)) == 521


/-
Prove the logical equivalence of `carryselect n k` and `ripplecarry n` using the
Davis-Putnam procedure.
-/
def prove_equiv (impl: PFormula → Bool) (n k: Nat) : Bool := impl (mk_carryselect_ripple_equivalence n k)

def prove (impl: PFormula → Bool) (n k: Nat) : IO Unit := do
  IO.print s!"prove {n} {k}: "
  let res := prove_equiv impl n k
  IO.println (if res then "equivalent" else "not equivalent")

/-
On small adder equiv. problems time DP < time DPLI < time DPLL
On larger adder equiv. problems time DPLI < time DPLL < time DP

Output:

Verification with DP:
====================
prove 3 1: equivalent
time:  58.3ms
prove 3 2: equivalent
time:  44.8ms
prove 3 3: equivalent
time:  69.1ms
prove 4 2: equivalent
time:  255ms
prove 4 3: equivalent
time:  172ms
prove 5 2: equivalent
time:  1.13s
prove 5 3: equivalent
time:  10.1s

Verification with DPLL:
====================
prove 3 1: equivalent
time:  97.1ms
prove 3 2: equivalent
time:  93ms
prove 3 3: equivalent
time:  122ms
prove 4 2: equivalent
time:  559ms
prove 4 3: equivalent
time:  560ms
prove 5 2: equivalent
time:  2.4s
prove 5 3: equivalent
time:  2.78s

Verification with iterative DPLL:
=====================
prove 3 1: equivalent
time:  76.9ms
prove 3 2: equivalent
time:  60.6ms
prove 3 3: equivalent
time:  68ms
prove 4 2: equivalent
time:  357ms
prove 4 3: equivalent
time:  336ms
prove 5 2: equivalent
time:  1.71s
prove 5 3: equivalent
time:  1.75s

Verification with backjumping DPLL:
=====================
prove 3 1: equivalent
time:  84.1ms
prove 3 2: equivalent
time:  84.7ms
prove 3 3: equivalent
time:  92.2ms
prove 4 2: equivalent
time:  602ms
prove 4 3: equivalent
time:  594ms
prove 5 2: equivalent
time:  5.25s
prove 5 3: equivalent
time:  5.37s

Verification with backjumping and learning DPLL:
=====================
prove 5 3: equivalent
time:  2.58s
-/
def main : IO Unit := do
  IO.println "Verification with DP:\n====================="
  -- timeit "time: " (prove dptaut 3 1)
  -- timeit "time: " (prove dptaut 3 2)
  -- timeit "time: " (prove dptaut 3 3)
  -- timeit "time: " (prove dptaut 4 2)
  -- timeit "time: " (prove dptaut 4 3)
  -- timeit "time: " (prove dptaut 5 2)
  timeit "time: " (prove dptaut 5 3)

  IO.println "\nVerification with DPLL:\n====================="
  -- timeit "time: " (prove dplltaut 3 1)
  -- timeit "time: " (prove dplltaut 3 2)
  -- timeit "time: " (prove dplltaut 3 3)
  -- timeit "time: " (prove dplltaut 4 2)
  -- timeit "time: " (prove dplltaut 4 3)
  -- timeit "time: " (prove dplltaut 5 2)
  timeit "time: " (prove dplltaut 5 3)

  IO.println "\nVerification with iterative DPLL:\n====================="
  -- timeit "time: " (prove dplitaut 3 1)
  -- timeit "time: " (prove dplitaut 3 2)
  -- timeit "time: " (prove dplitaut 3 3)
  -- timeit "time: " (prove dplitaut 4 2)
  -- timeit "time: " (prove dplitaut 4 3)
  -- timeit "time: " (prove dplitaut 5 2)
  timeit "time: " (prove dplitaut 5 3)

  IO.println "\nVerification with backjumping DPLL:\n====================="
  -- timeit "time: " (prove dplbtaut 3 1)
  -- timeit "time: " (prove dplbtaut 3 2)
  -- timeit "time: " (prove dplbtaut 3 3)
  -- timeit "time: " (prove dplbtaut 4 2)
  -- timeit "time: " (prove dplbtaut 4 3)
  -- timeit "time: " (prove dplbtaut 5 2)
  timeit "time: " (prove dplbtaut 5 3)

  IO.println "\nVerification with backjumping and learning DPLL:\n====================="
  timeit "time: " (prove dplb'taut 5 3)

/-
Note: removing the `affirmative_negative_rule` from DP improves
performance slightly (~20%) in these problems:

prove 3 1: equivalent
time:  45.6ms
prove 3 2: equivalent
time:  34ms
prove 3 3: equivalent
time:  53.9ms
prove 4 2: equivalent
time:  203ms
prove 4 3: equivalent
time:  136ms
prove 5 2: equivalent
time:  901ms
prove 5 3: equivalent
time:  8.34s

-/
