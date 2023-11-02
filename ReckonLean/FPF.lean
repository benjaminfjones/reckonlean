/-
------------------------------------------------------------------------
Polymorphic Finite Partial Functions
------------------------------------------------------------------------

This module contains an implementation of polymorphic finite partial
functions. They serve as the representation for valuations and substitions,
among other things.

The original implementation in the Handbook uses Patricia trees. The one here
is based on the builtin `Lean.Data.HashMap` type. The main difference being
that the Patricia tree representation is canonical, whereas the HashMap
representation depends on insertion order.

Extensional equality obviously works in both representations. It remains to see
whether that performs well enough to substitute for structural equality.
-/

import Lean.Data.HashMap
import ReckonLean.Common

open Lean

namespace Lean.HashMap
  def mapVals {α: Type} [BEq α] [Hashable α] (f : β → γ) (xs : HashMap α β) : HashMap α γ :=
    mkHashMap (capacity := xs.size) |> xs.fold fun acc k v => acc.insert k (f v)
end Lean.HashMap

namespace FPF

structure Func (γ: Type) (δ: Type) [BEq γ] [Hashable γ] where
  map : HashMap γ δ

variable {α: Type} [BEq α] [Hashable α]
variable {β: Type}

/-!
The completely undefined function
-/
def empty : Func α β := {map := HashMap.empty}
/-! Alias for empty -/
def undefined : Func α β := empty
/-! Compose `func` with with a complete function on the range. -/
def mapf (f: β → γ) (func: Func α β) : Func α γ := { map := HashMap.mapVals f func.map }
/-! Fold over the graph of `func`-/
def fold {δ : Type} (f : δ → α → β → δ) (init : δ) (func : Func α β) : δ := HashMap.fold f init func.map

/- ------------------------------------------------------------------------- -/
/- Mapping to sorted-list representation of the graph, domain and range.     -/
/- ------------------------------------------------------------------------- -/

instance [Ord α] [Ord β]: Ord (α × β) where
  compare t1 t2 := match compare t1.fst t2.fst with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare t1.snd t2.snd

instance [BEq α] [BEq β]: BEq (α × β) where
  beq t1 t2 := BEq.beq t1.fst t2.fst && BEq.beq t1.snd t2.snd

/-!
Graph of the function as a set of (domain, range) tuples
-/
def graph [Ord α] [BEq α] [Ord β] [BEq β] (f: Func α β) : List (α × β) :=
  Set.setify (fold (fun a x y => (x, y) :: a) [] f)
def dom [Ord α] [BEq α] [Ord β] [BEq β] (f: Func α β) : List α :=
  Set.setify (fold (fun a x _y => x :: a) [] f)
def ran [Ord α] [BEq α] [Ord β] [BEq β] (f: Func α β) : List β :=
  Set.setify (fold (fun a _x y => y :: a) [] f)

/-!
Apply an FPF with default function in case the function isn't defined.
-/
def applyd (f: Func α β) (default: α → β) (x: α) : β :=
  match f.map.find? x with
  | some v => v
  | none => default x

/-!
Try to apply `f` to `x`
-/
def apply? (f: Func α β) (x: α) : Option β := f.map.find? x

/-!
Apply `f` to `x`; panic if `f` is not defined there.
-/
def apply! [Inhabited β] (f: Func α β) (x: α) : β := f.map.find! x

/-!
Is `f` defined at `x`?
-/
def defined (f: Func α β) (x: α) : Bool := f.map.contains x

/-
Remove `x` from the domain. This function is particularly complicated
to implement in the patricia tree representation.
-/
def undefine (f: Func α β) (x: α) : Func α β := ⟨ f.map.erase x ⟩

/-!
Extend (or redefine) the function with a single domain, range pair; Aka `|->`.

For example `(x0 |-> y0) func` is the function mapping `x0` to `y0` and every
`x' { x ∈ domain(func) | x != x0 }` to `func(x)`.
-/
def ins (x: α) (y: β) : Func α β → Func α β
  | f => { f with map := f.map.insert x y}
infixr:100 " |-> " => ins

#check (1 |-> 2) (empty : Func Nat Nat)

/-
Combine two functions pointwise using the binary operator `op`. The `filter` is
used to filter out domain, range pairs after applying the `op`.
-/
def combine (op: β → β → β) (filter: β → Bool) (f1 f2: Func α β) : Func α β :=
  let combiner (func1: Func α β) (x2: α) (y2: β) :=
    match apply? func1 x2 with
    | some y1 => let y' := op y1 y2
                 if filter y' then undefine func1 x2 else (x2 |-> y') func1
    | none => (x2 |-> y2) func1
  fold combiner f1 f2  -- f1 is the `init`, f2 is folded over

/-
Example: [some 3, none, some 0]
-/
#eval let f := combine (fun y y' => y + y') (fun x => x > 5)
                 ((1 |-> 2) ((2 |-> 1) empty))
                 ((1 |-> 1) ((2 |-> 6) ((3 |-> 0) empty)))
      [apply? f 1, apply? f 2, apply? f 3]

/-!
Point function: `(x |=> y)` is the function that is only defined at `x` and
maps `x` to `y`.
-/
def point (x: α) (y: β) : Func α β := (x |-> y) empty
infixr:100 " |=> " => point

#eval apply! (0 |=> 1) 0  -- 1
#eval apply? (0 |=> 1) 1  -- none

/-!
Construct a function from a pair of domain, range lists. Zip is used which
truncates the input lists if they are not of equal length.
-/
def from_lists (xs: List α) (ys: List β) : Func α β :=
  List.foldr (fun (x, y) f => (x |-> y) f) empty (List.zip xs ys)

/-!
Converts a function into an association list

In general, this is different than `graph` whose output is a set.
-/
def to_list (f: Func α β) : List (α × β) := f.map.toList

#eval apply! (from_lists [0] [1]) 0  -- 1
#eval apply? (from_lists [0] [1]) 1  -- none

/-
Same `combine` example as above:
[(3, 0), (1, 3)]
-/
#eval to_list (combine (fun y y' => y + y') (fun x => x > 5)
                 (from_lists [1,2] [2,1])
                 (from_lists [1,2,3] [1,6,0]))

/-!
Choose an arbitrary domain, range pair
-/
def choose [Inhabited α] [Inhabited β] (f: Func α β) : α × β :=
  match to_list f with
  | [] => panic! "choose: completely undefined function"
  | t :: _ => t

end FPF
