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

end FPF
