import ReckonLean.Common
import ReckonLean.Fol
import ReckonLean.FPF

open FPF
open Term

/-!
Unification and it's applications to first order validity checking.

An `env` is a finite partial map from variable names to terms (a.k.a. an
instantiation). Given an `env`, define a relation -> on variables so that x ->
y if x |-> t in env and y in FVT(t).

e.g. if x |-> f(u, v) then we have x -> u and x -> v.

We want `env` to have no cycles in the sense that the refl-transitive closure of
-> has no cycles.

If we have a acyclic env and want to add x |-> t to it, consider conditions:

(1) there is no existing assignment x |-> s
(2) there is no variable y in FVT(t) such that y ->* x

These suffice to ensure that (x |-> t) env is acyclic.
-/

/--
"Is trivial addition to env"

Returns:
- true is t = Var x
- false if condition (2) holds
- panic if env is cyclic
-/
partial def istriv (env : Func String Term) (x : String) (t : Term) : Bool :=
  match t with
  | Var y => y == x || (defined env y && istriv env x (apply! env y))
  | Fn _f args => List.any args (fun a => istriv env x a) && panic! "cyclic"

def env0 := ("y" |-> Var "z") (("x" |-> Var "y") empty)
#guard istriv env0 "z" (Var "z") == true
#guard istriv env0 "z" (Var "x") == true  -- benign cycle?
#guard istriv env0 "z" (Var "w") == false

def env1 := ("u" |-> Var "y") (("x" |-> Fn "f" [Var "u", Var "v"]) empty)
#guard istriv env1 "v" (Var "w") == false
/- #guard istriv env1 "v" (Var "x") == false  -- PANIC -/
