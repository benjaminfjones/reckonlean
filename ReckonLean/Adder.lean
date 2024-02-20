import ReckonLean.Common
import ReckonLean.Formulas
import ReckonLean.Prop
import ReckonLean.Dpll

open Formula

/-
   Verification of adder circuit equivalence
-/

/- ------------------------------------------------------------------------- -/
/- Half & Full Adders                                                        -/
/- ------------------------------------------------------------------------- -/

/- Half sum & carry table

   x  | y  | s  | c  |
   -------------------
   0  | 0  | 0  | 0  |
   0  | 1  | 1  | 0  |
   1  | 0  | 1  | 0  |
   1  | 1  | 0  | 1  |
-/
def halfsum (x y: PFormula) : PFormula := Formula.Not (Formula.Iff x y)
def halfcarry (x y: PFormula) : PFormula := Formula.And x y

/- Relation encoding the half adder in terms of inputs / outputs.

   s <=> halfsum x y ∧ c <=> halfcarry x y
-/
def halfadd (x y sumout cout: PFormula) :=
  Formula.And (Formula.Iff sumout (halfsum x y)) (Formula.Iff cout (halfcarry x y))

/- Full sum and carry take two inputs bits and an input carry -/
def fullsum (x y cin: PFormula) := halfsum (halfsum x y) cin

/- There is an output carry <=> 2 of 3 inputs are true -/
def fullcarry (x y cin: PFormula) := Formula.Or (Formula.And x y) (Formula.And (Or x y) cin)

/- Relation encoding the full carry -/
def fulladd (x y cin sumout cout: PFormula) : PFormula :=
  Formula.And (.Iff sumout (fullsum x y cin)) (.Iff cout (fullcarry x y cin))


/- ------------------------------------------------------------------------- -/
/- Ripple Carry Adder                                                        -/
/- ------------------------------------------------------------------------- -/

def conjoin (f: Nat → PFormula) (idxs: List Nat) := list_conj (List.map f idxs)

/- Relation encoding a ripplecarry adder over `n` bits.

   The inputs `x`, `y`, etc are functions from bit index => atomic proposition
-/
def ripplecarry (n: Nat) (x y cin sumout: Nat → PFormula) : PFormula :=
  let mkconj i := fulladd (x i) (y i) (cin i) (sumout i) (cin (i + 1))
  conjoin mkconj (List.range n)

/- Ripple carry with input carry = 0 -/
def ripplecarry0 (n: Nat) (x y cin sumout: Nat → PFormula) : PFormula :=
  psimplify (ripplecarry n x y (fun i => if i == 0 then False else cin i) sumout)

/- Ripple carry with input carry = 1 -/
def ripplecarry1 (n: Nat) (x y cin sumout: Nat → PFormula) : PFormula :=
  psimplify (ripplecarry n x y (fun i => if i == 0 then True else cin i) sumout)

def mk_bit (pref: String) (i: Nat) : PFormula := Formula.Atom ⟨ s!"{pref}_{i}" ⟩

def mk_bit2 (pref: String) (i j: Nat) : PFormula :=
  Atom ⟨ s!"{pref}_{i}_{j}" ⟩

/- ------------------------------------------------------------------------- -/
/- Carry-select adder                                                        -/
/-                                                                           -/
/- Carry-select is an optimization that reduces the number of cycles needed  -/
/- to compute an n-bit add circuit.                                          -/
/-                                                                           -/
/- Carry-select performs a k-bit ripple carry for each possible carry input, -/
/- muxes the result based on the actual carry input, and repeats for each k  -/
/- (or less) bit block of the n total bits.                                  -/
/- ------------------------------------------------------------------------- -/

/- Multiplex the input formulas based on a selector proposition -/
def mux (sel in0 in1: PFormula) : PFormula := Formula.Or (.And (Not sel) in0) (.And sel in1)

/- Apply a proposition maker function with bits offset by n -/
def offset (n: Nat) (x: Nat → PFormula) (i: Nat) : PFormula := x (n + i)

/-
Carry-select adder over `n`-bits with blocks of size `k`.
-/
partial def carryselect (n k: Nat) (x y c0 c1 s0 s1 c s: Nat → PFormula) : PFormula :=
  let k' := min n k
  let fm :=
    Formula.And
      (.And (ripplecarry0 k' x y c0 s0) (ripplecarry1 k' x y c1 s1))
      (.And
        (.Iff (c k') (mux (c 0) (c0 k') (c1 k')))
        (conjoin (fun i => .Iff (s i) (mux (c 0) (s0 i) (s1 i))) (List.range k')))
  if k' < k then fm  -- in particular, `n < k`
  else
    .And
      fm
      (carryselect (n - k) k (offset k x) (offset k y) (offset k c0)
          (offset k c1) (offset k s0) (offset k s1) (offset k c) (offset k s) )


/- Examples -/

namespace Examples

/-
Formula for the `ripplecarry0 1` relation.

sumout is ~(x <=> y)
carry out is x ∧ y
-/
#guard
  let x := mk_bit "x"
  let y := mk_bit "y"
  let cin := mk_bit "cin"
  let sumout := mk_bit "sumout"
  print_pf (ripplecarry0 1 x y cin sumout)
  == "<<(sumout_0 <=> ~(x_0 <=> y_0)) ∧ (cin_1 <=> x_0 ∧ y_0)>>"

end Examples
