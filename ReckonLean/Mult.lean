import Std.Tactic.GuardExpr

import ReckonLean.Adder
import ReckonLean.Dpll

/- ------------------------------------------------------------------------- -/
/- Ripple carry stage that separates off the final result. This is used to   -/
/- add rows in the usual Nat multiplation algorithm.                         -/
/-                                                                           -/
/-       UUUUUUUUUUUUUUUUUUUU  (u)                                           -/
/-    +  VVVVVVVVVVVVVVVVVVVV  (v)                                           -/
/-                                                                           -/
/-    = WWWWWWWWWWWWWWWWWWWW   (w)                                           -/
/-    +                     Z  (z)                                           -/
/- ------------------------------------------------------------------------- -/

def rippleshift (n: Nat) (u v c w: Nat → PFormula) (z : PFormula) : PFormula :=
  ripplecarry0 n u v
    (fun i => if i == n then w (n - 1) else c (i + 1))
    (fun i => if i == 0 then z else w (i - 1))

/- ------------------------------------------------------------------------- -/
/- Naive multiplier based on repeated ripple carry.                          -/
/- ------------------------------------------------------------------------- -/

def multiplier (n: Nat) (x u v: Nat → Nat → PFormula) (out: Nat → PFormula): PFormula :=
  if n == 1 then
    --      A0   Xij := Ai * Bj = Ai ∧ Bj
    -- *    B0
    --
    -- = P1 P0   ==> P0 = X00 ∧ ¬ P1
    .And (.Iff (out 0) (x 0 0)) (.Not (out 1))
  else
    psimplify
     (.And (.Iff (out 0) (x 0 0))  -- relation for the 0th bit of the result
          (.And (rippleshift n
                 (fun i => if i == n - 1 then .False else x 0 (i + 1))
                 (x 1) (v 2) (u 2) (out 1))
               (if n == 2 then
                 .And (.Iff (out 2) (u 2 0)) (.Iff (out 3) (u 2 1))
               else
                 conjoin (fun k =>
                   rippleshift n (u k) (x k) (v (k + 1))
                     (if k == n - 1 then fun i => out (n + i)
                      else u (k + 1))
                     (out k)) (List.range_from_nat 2 (n - 1)))))

/- ------------------------------------------------------------------------- -/
/- Primality examples.                                                       -/
/- ------------------------------------------------------------------------- -/

/- Number of bits required to represent a Nat -/
def bitlength (x: Nat) : Nat := if h: !(x == 0) then 1 + bitlength (x / 2) else 0
decreasing_by
  simp_wf
  rewrite [Nat.not_beq_eq_true_eq] at h
  apply Nat.div_lt_self
  . exact Nat.zero_lt_of_ne_zero h
  . apply Nat.lt_succ_of_le; apply Nat.le_refl  -- or `simp_arith`

example : bitlength 0 = 0 := by rfl
example : bitlength 1 = 1 := by rfl
example : bitlength 3 = 2 := by rfl
example : bitlength 101 = 7 := by rfl

/-! Return the `n`th bit of `x` as a Bool -/
def bit (n x: Nat) : Bool :=
  natbit n x == 1
where
  natbit n x := match n with
    | 0 => x &&& 1
    | m + 1 => natbit m (x >>> 1)

example : bit 0 3 = true := by rfl
example : bit 1 3 = true := by rfl
example : bit 2 3 = false := by rfl

/-! Formula asserting that a propositional bitvector `x` is congruent to Nat `m` mod 2^`n` -/
def congruent_to (x: Nat → PFormula) (m n: Nat) : PFormula :=
  conjoin (fun i => if bit i m then x i else .Not (x i))
          (List.range_from_nat 0 (n - 1))

/-!
Formula asserting that a natural number `p` is prime.

This is encoded by asserting that if `p` is representable in `n` bits,
there do no exist natural numbers `x, y`, s.t. `2 <= x <= p/2`, `2 <= y <= p/2` and
`p = x * y`. The inequalities on `x, y` imply they are representable in `n-1` bits
and we only need to test their product modulo `2^n`.
-/
def prime (p: Nat) : PFormula :=
  let x := mk_bit "x"
  let y := mk_bit "y"
  let out := mk_bit "out"
  let m i j := Formula.And (x i) ( y j)
  let u := mk_bit2 "u"
  let v := mk_bit2 "v"
  let n := bitlength p
  .Not (.And (multiplier (n-1) m u v out)
             (congruent_to out p (max n (2 * n - 2))))

#guard not (dptaut (prime 1))
#guard dptaut (prime 2)
#guard dptaut (prime 3)
#guard not (dptaut (prime 4))
-- etc
