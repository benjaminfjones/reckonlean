import Std.Data.MLList.Basic

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

-- There is no Monad List instance in Prelude because `List` is eager. There is an instance for LazyList.
#check (Monad List)  -- this is just a Type, there is no instance yet
#check (Bind List)   -- also just a type

-- see Std4 MLList, a lazy list
#check (MLList.instMonadMLList : Monad (MLList Id))

/-
invalid `do` notation, expected type is not a monad application
  List Nat
You can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad.
-/
-- #eval (do pure [1] : List Nat)

instance : Monad List where
  pure := List.pure
  bind := List.bind

def nondet : List Nat :=
  [1,2,3] >>= fun a =>
  [10, 20, 30] >>= fun b =>
  pure (a + b)

#eval nondet

section Panic

-- a contradiction can't be found in the second case; the conclusion does not hold
-- because if A[i]! panics then it's value is `default` as far as the type system is
-- concerned
example (i: Nat) (x: Int) (A: Array Int) : A[i]! = x → A[i]? = some x := by
  intro h
  unfold getElem! at h
  split at h
  . unfold getElem?; simp_all
  . sorry  -- h: x = outOfBounds

theorem getD_eq_get? (a : Array α) (n: Nat) (d: α) : a.getD n d = (a.get? n).getD d := by
  simp [Array.get?, Array.getD, Option.getD]; split
  . rfl
  . simp

theorem get!_eq_getD [Inhabited α] (a : Array α) (n: Nat): a.get! n = a.getD n default := rfl

theorem get!_eq_get? [Inhabited α] (a : Array α) (n: Nat): a.get! n = (a.get? n).getD default := by
  simp [get!_eq_getD, getD_eq_get?]

example (i: Nat) (x: Int) (A: Array Int) : A[i]! = x → (A[i]?).getD default = x := by
  intro h
  rw [← h]
  exact (get!_eq_get? A i).symm

end Panic
