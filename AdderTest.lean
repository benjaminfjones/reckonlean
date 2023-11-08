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
      (conjoin (fun i => .Iff (s i) (s2 i)) (List.range_offset 0 (n-1)))
    )

-- #eval List.length (atoms (mk_carryselect_ripple_equivalence 4 2))  -- 39

def prove_equiv (n k: Nat) : Bool := dptaut (mk_carryselect_ripple_equivalence n k)

def prove (n k: Nat) : IO Unit := do
  let res := prove_equiv n k
  IO.println (if res then "equivalent" else "not equivalent")

-- #eval timeit "" (prove 3 2)  -- 1.1 s in the eval VM, 0.06 s compiled
-- #eval timeit "" (prove 4 2)  -- 5.6 s in the eval VM, 0.2 s compiled

-- TODO: add timing, other combinations of n, k
def main : IO Unit := prove 4 2
