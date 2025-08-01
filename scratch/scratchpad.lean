import Batteries.Data.MLList.Basic

namespace PolymorphicDeriving

  structure Foo (a: Type) where
    foo: a
  deriving Repr

  #eval ({foo:=1} : Foo Nat)

  inductive Bar (a: Type) where
    | A
    | B (b: a)
    | C (s: String) (c: a)
  deriving Repr, BEq, Ord

  #eval Bar.B 1 == Bar.B 2
  #eval Bar.C "see" 1 == Bar.B 2
  #eval compare (Bar.C "see" 1) (Bar.B 2) == .gt  -- true
  #eval compare (Bar.A) (Bar.B 2) == .lt  -- true
  #eval compare (Bar.A : Bar Nat) (Bar.A) == .eq  -- true

end PolymorphicDeriving

namespace StringManip

#check Substring

def sliceString (str: String) (startPos stopPos: String.Pos) : Substring :=
  {str, startPos, stopPos}

def sliceString' (str: String) (startByte stopByte: Nat) : Substring :=
  {str, startPos := {byteIdx := startByte}, stopPos := {byteIdx := stopByte}}

#eval sliceString' "foobar" 0 1              -- "f".toSubstring
#eval (sliceString' "foobar" 0 1).toString   -- "f"
#eval (sliceString' "foobar" 0 10).toString  -- stops at the end: "foobar"

end StringManip

#check Nat.max
#check String.toNat?

-- slash dot!
#eval (· * 2) 5


section Panic

theorem getD_eq_get? (a : Array α) (n: Nat) (d: α) : a.getD n d = (a[n]?).getD d := by
  simp [Array.getD, Option.getD]
  split <;> grind

theorem get!_eq_getD [Inhabited α] (a : Array α) (n: Nat): a[n]! = a.getD n default := rfl

theorem get!_eq_get? [Inhabited α] (a : Array α) (n: Nat):  a[n]! = (a[n]?).getD default := by
  refine Eq.symm ((fun {α} {o} {a b} => Option.getD_eq_iff.mpr) ?_)
  simp
  by_cases (a.size ≤ n)
  . apply Or.inr
    constructor
    . assumption
    . grind
  . sorry





example (i: Nat) (x: Int) (A: Array Int) : A[i]! = x → (A[i]?).getD default = x := by
  intro h
  rw [← h]
  exact (get!_eq_get? A i).symm

end Panic
