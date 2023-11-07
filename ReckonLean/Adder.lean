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
def fulladd x y cin sumout cout :=
  And (Iff (sumout, fullsum x y cin), Iff (cout, fullcarry x y cin))

def conjoin f idxs := list_conj (List.map f idxs)

/- ------------------------------------------------------------------------- -/
/- Ripple Carry Adder                                                        -/
/- ------------------------------------------------------------------------- -/

/- Relation encoding a ripplecarry adder over `n` bits.

   The inputs `x`, `y`, etc are functions from bit index => atomic proposition
-/
def ripplecarry n x y cin sumout :=
  let mkconj i := fulladd (x i) (y i) (cin i) (sumout i) (cin (i + 1))
  conjoin mkconj (0 -- (n - 1))

/- Ripple carry with input carry := 0 -/
def ripplecarry0 n x y cin sumout :=
  psimplify (ripplecarry n x y (fun i => if i := 0 then False else cin i) sumout)

/- Ripple carry with input carry := 1 -/
def ripplecarry1 n x y cin sumout :=
  psimplify (ripplecarry n x y (fun i => if i := 0 then True else cin i) sumout)

def mk_bit prefix i := Atom (P (prefix ^ "_" ^ string_of_int i))

def _mk_bit2 prefix i j :=
  Atom (P (prefix ^ "_" ^ string_of_int i ^ "_" ^ string_of_int j))

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
def mux sel in0 in1 := Or (And (Not sel, in0), And (sel, in1))

/- Apply a proposition maker function with bits offset by n -/
def offset n x i := x (n + i)

/- I weep at the signature of this function -/
def rec carryselect n k x y c0 c1 s0 s1 c s :=
  let k' := min n k
  let fm :=
    And
      ( And (ripplecarry0 k' x y c0 s0, ripplecarry1 k' x y c1 s1),
        And
          ( Iff (c k', mux (c 0) (c0 k') (c1 k')),
            conjoin (fun i => Iff (s i, mux (c 0) (s0 i) (s1 i))) (0 -- (k' - 1))
          ) )

  if k' < k then fm
  else
    And
      ( fm,
        carryselect (n - k) k (offset k x) (offset k y) (offset k c0)
          (offset k c1) (offset k s0) (offset k s1) (offset k c) (offset k s) )
