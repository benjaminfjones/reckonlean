/-
------------------------------------------------------------------------
Polymorphic Finite Partial Functions
------------------------------------------------------------------------
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

def empty : Func α β := {map := HashMap.empty}
def undefined : Func α β := empty
def mapf (f: β → γ) (m: Func α β) : Func α γ := { map := HashMap.mapVals f m.map }
def fold {δ : Type} (f : δ → α → β → δ) (init : δ) (m : Func α β) : δ := HashMap.fold f init m.map

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

/- Graph of the function as a set of (domain, range) tuples -/
def graph [Ord α] [BEq α] [Ord β] [BEq β] (f: Func α β) : List (α × β) :=
  Set.setify (fold (fun a x y => (x, y) :: a) [] f)
def dom [Ord α] [BEq α] [Ord β] [BEq β] (f: Func α β) : List α :=
  Set.setify (fold (fun a x _y => x :: a) [] f)
def ran [Ord α] [BEq α] [Ord β] [BEq β] (f: Func α β) : List β :=
  Set.setify (fold (fun a _x y => y :: a) [] f)

/- Apply an FPF with default function in case the function isn't defined -/
def applyd (f: Func α β) (default: α → β) (x: α) : β :=
  match f.map.find? x with
  | some v => v
  | none => default x

def apply? (f: Func α β) (x: α) : Option β := f.map.find? x

def apply! [Inhabited β] (f: Func α β) (x: α) : β := f.map.find! x

def defined (f: Func α β) (x: α) : Bool := f.map.contains x

/-
Remove `x` from the domain. This function is particularly complicated
to implement in the patricia tree representation.
-/
def undefine (f: Func α β) (x: α) : Func α β := ⟨ f.map.erase x ⟩

/- Extend (or redefine) the function with a single domain, range pair. Aka `|->` -/
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

/- Point function -/
def point (x: α) (y: β) : Func α β := (x |-> y) empty
infixr:100 " |=> " => point

#eval apply! (0 |=> 1) 0  -- 1
#eval apply? (0 |=> 1) 1  -- none

def from_lists (xs: List α) (ys: List β) : Func α β :=
  List.foldr (fun (x, y) f => (x |-> y) f) empty (List.zip xs ys)

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

/- Choose an arbitrary domain, range pair -/
def choose [Inhabited α] [Inhabited β] (f: Func α β) : α × β :=
  match to_list f with
  | [] => panic! "choose: completely undefined function"
  | t :: _ => t

end FPF
