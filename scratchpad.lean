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
