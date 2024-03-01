import Std.Tactic.GuardExpr  -- provides #guard
import Std.Tactic.Omega
import Std.Tactic.SimpTrace

def non (p : α → Bool) (x: α) : Bool := not (p x)
example : List.map (non (fun x => x % 2 = 0)) [0, 1, 2] = [false, true, false] := by rfl

namespace String

  def sliceString (str: String) (startByte stopByte: Nat) : Substring :=
    {str, startPos := {byteIdx := startByte}, stopPos := {byteIdx := stopByte}}

  def copySlice (str: String) (startByte stopByte: Nat) : String :=
    (sliceString str startByte stopByte).toString

end String

namespace List

  /- Convenient List alises -/
  def mem {α: Type} [BEq α] (x: α) (xs: List α) : Bool := List.contains xs x

  /- Like `foldl` but has no base case which is convenient in certain places -/
  def end_itlist [Inhabited α] (f: α → α → α) : List α → α
    | [] => panic! "end_itlist"
    | [x] => x
    | h :: t => f h (end_itlist f t)

  def all_pairs (f : α → β → γ) (l1: List α) (l2: List β): List γ :=
    match l1 with
    | [] => []
    | h1 :: t1 => foldl (fun a x => f h1 x :: a) (all_pairs f t1 l2) l2

  example : all_pairs (fun x y => x + y) [1,2] [-1, -3] =
    [-2, 0, -1, 1] := by rfl
  example : all_pairs (fun x y => x * y) [1,2,3] [-1, -2, -3] =
    [-3, -2, -1, -6, -4, -2, -9, -6, -3] := by rfl

  def distinct_pairs : List α -> List (α × α)
    | [] => []
    | x :: t => foldl (fun a y => (x, y) :: a) (distinct_pairs t) t

  example : distinct_pairs [1, 2, 3] = [(1, 3), (1, 2), (2, 3)] := by rfl
  example : distinct_pairs [0, 1] = [(0, 1)] := by rfl
  example : distinct_pairs [0] = [] := by rfl


/- ------------------------------------------------------------------------- -/
/- Find list member that maximizes or minimizes a function.                  -/
/- ------------------------------------------------------------------------- -/

/- Optimize an objective function given an ordering on objective values. -/
def optimize (ord: β → β → Bool) (f : α → β) : List α → Option α
  | [] => none
  | x :: rest =>
    let rest_obj_vals := List.mapTR (fun x => (x, f x)) rest
    some ((foldl (fun p'@(_', y') p@(_, y) => if ord y y' then p else p') (x, f x)
      rest_obj_vals).fst)

def maximize [Ord β] (f: α → β) (l: List α) : Option α := optimize (compare · · == .gt) f l
def minimize [Ord β] (f: α → β) (l: List α) : Option α := optimize (compare · · == .lt) f l

#guard maximize id [1,2,3,4] == some 4
#guard minimize id [1,2,3,4] == some 1

end List

/-
Sets as sorted lists

This implementation is used in order not to have to depend on Std4 or Mathlib4
for a set datatype. It is fast enough the purposes of this project.
-/

namespace Set
open Ord
open Ordering

variable {α: Type} [Ord α] [BEq α]

/- Remove consecutive duplicates from a list; on sorted lists this returns the set of unique elements -/
def uniq : List α → List α
  | l@(x :: t@(y :: _)) =>
      let t' := uniq t
      if compare x y == .eq then t' else if t' == t then l else x :: t'
  | l => l

/- Merging of sorted lists (maintaining repetitions) -/
partial def merge(l1 l2: List α) : List α :=
  match l1 with
  | [] => l2
  | h1 :: t1 => (
      match l2 with
      | [] => l1
      | h2 :: t2 =>
          if (compare h1 h2).isLE then h1 :: merge t1 l2 else h2 :: merge l1 t2)
-- termination_by merge l1 l2 => l1.length + l2.length

#guard merge [] [1,2] == [1, 2]  -- true
#guard merge [5] [1,2] == [1, 2, 5]  -- true
#guard merge [1,2] [1,3] == [1, 1, 2, 3]

partial def mergepairs : List (List α) → List (List α) → List α
  | s::[], [] => s
  | l, [] => mergepairs [] l
  | l, [ s1 ] => mergepairs (s1 :: l) []
  | l, s1 :: s2 :: ss => mergepairs (merge s1 s2 :: l) ss

/- Bottom-up mergesort -/
def sort : List α → List α
  | [] => []
  | l => mergepairs [] ((fun x => [ x ]) <$> l)

#guard sort [4, 3, 2, 1] == [1, 2, 3, 4]
#guard sort [1, 3, 2, 1] == [1, 1, 2, 3]
#guard sort [1] == [1]

/--
A list is canonical iff. it is sorted and has unique elements.

`canonical` is tail-recursive and linear-time.
-/
def canonical : List α → Bool
  | x :: rest@(y :: _) =>
    if compare x y == lt then canonical rest else false
  | _ => true

/-- Construct a set, represented as a canonical list. -/
def setify (l: List α) : List α :=
  if canonical l then l
  else
    uniq <| sort l

#guard setify [1, 3, 2, 1] == [1, 2, 3]  -- true

def set_image [Ord β] [BEq β] (f: α -> β) (s : List α) := setify (List.mapTR f s)

#guard set_image (fun _ => 0) [1, 3, 2, 1] == [0]

/-!
Construct the union of two lists, as a canonical set

Note: `union` and related functions are very much not tail recursive!
For example, this causes stack overflow:

```
#eval (union (List.range 3700) (List.range 210858).reverse).length
```
-/
def union : List α → List α → List α
  | s1, s2 => aux_union (setify s1) (setify s2)
where
  aux_union l1 l2 :=
    match hc : (l1, l2) with
    | ([], _) => l2
    | (_, []) => l1
    | (h1 :: t1, h2 :: t2) =>
        have _ : t1.length < t1.length + 1 := Nat.lt_succ_self _
        have _ : t2.length < t2.length + 1 := Nat.lt_succ_self _
        have _ : t1.length < l1.length := by
          have hl : l1 = h1 :: t1 := congrArg Prod.fst hc
          rw [hl, List.length_cons h1 t1]
          apply Nat.lt_succ_self
        have _ : t2.length < l2.length := by
          have hl : l2 = h2 :: t2 := congrArg Prod.snd hc
          rw [hl, List.length_cons h2 t2]
          apply Nat.lt_succ_self

        if h1 == h2 then
          have _ : t1.length + t2.length < l1.length + l2.length := by
            apply Nat.add_lt_add
            assumption; assumption

          h1 :: aux_union t1 t2
        else if compare h1 h2 == lt then
          have _ : t1.length + l2.length < l1.length + l2.length := by
            apply Nat.add_lt_add_right
            assumption

          h1 :: aux_union t1 l2
        else
          have _ : l1.length + t2.length < l1.length + l2.length := by
            apply Nat.add_lt_add_left
            assumption

          h2 :: aux_union l1 t2
  termination_by l1.length + l2.length

#guard union [1,2,3] [4,5] == [1, 2, 3, 4, 5]
#guard union [1,2,3] [1, 2, 3] == [1, 2, 3]

def unions (s: List (List α)) : List α := setify (List.foldl List.appendTR [] s)

#guard unions [[1,2,3], [4,5,6], [1,5,8]] == [1,2,3,4,5,6,8]

def list_compare : List α → List α → Ordering
    | [], [] => .eq
    | [], _  => .lt
    | _, [] => .gt
    | h1 :: t1, h2 :: t2 =>
      match compare h1 h2 with
        | .lt => .lt
        | .gt => .gt
        | .eq => list_compare t1 t2

instance {α : Type} [Ord α] : Ord (List α) where
  compare := list_compare

#guard compare [1,2,3] [1,2,3,4] == .lt
#guard compare [1,2,3,4] [1,2,3] == .gt
#guard compare [1,2,3,4] [1,2,3] == .gt
#guard compare [1,2,3] [1,2,3] == .eq
#guard sort [[1,2], [2,1], [], [3,2,1], [1,5,9]] == [[], [1, 2], [1, 5, 9], [2, 1], [3, 2, 1]]

/- Return a list of all subsets of given size. -/
def allsubsets (size: Int) (items: List α) : List (List α) :=
  aux size (setify items)
where
  aux sz xs :=
    if sz <= 0 then [ [] ]
    else if sz > xs.length then []
    else (
        match xs with
        | [] => []
        | x :: rest =>
            union
              (List.mapTR (union [ x ]) (aux (sz - 1) rest))
              (aux sz rest))
  termination_by xs.length

#guard allsubsets 4 [1,2,3] == []
#guard allsubsets 3 [1,2,3] == [[1, 2, 3]]
#guard allsubsets 2 [1,2,3] == [[1, 2], [1, 3], [2, 3]]
#guard allsubsets 0 [1,2,3] == [[]]


/-
Setify the input lists and return their intersection.

The termination proof for `intersect` and its recursive helper `aux`
is carried out below for the fun of it.
-/
def intersect (l1 l2: List α) : List α :=
  aux (setify l1) (setify l2)
where
  aux j1 j2 := match j1, j2 with
    | [], _ => []
    | _, [] => []
    | l1@(h1 :: t1), l2@(h2 :: t2) =>
        if h1 == h2 then
          have _ : t1.length + t2.length < 2 + t1.length + (1 + t2.length) := by simp_arith
          h1 :: aux t1 t2
        else
          if compare h1 h2 == lt then
            have _ : t1.length + l2.length < 1 + t1.length + l2.length := by simp_arith
            aux t1 l2
          else
            have _ : l1.length + t2.length < l1.length + (1 + t2.length) := by simp_arith
            aux l1 t2
  termination_by j1.length + j2.length

#guard intersect [1,2,3] [4,5] == []
#guard intersect [1,2,3] [3, 4,5] == [3]
#guard union [1,2,3] [1, 2, 3] == [1, 2, 3]

/-
Remove a set from another

Termination proof is similar to that of `intersect` but this time we don't
use the simplifier at all.
-/
def subtract : List α → List α → List α
  | s1, s2 => subaux (setify s1) (setify s2)
where
  subaux l1 l2 := match hc : (l1, l2) with
    | ([], _) => []
    | (_, []) => l1
    | (h1 :: t1, h2 :: t2) =>
        have _ : t1.length < l1.length := by
          have hl : l1 = h1 :: t1 := congrArg Prod.fst hc
          rw [hl, List.length_cons h1 t1]
          apply Nat.lt_succ_self
        have _ : t2.length < l2.length := by
          have hl : l2 = h2 :: t2 := congrArg Prod.snd hc
          rw [hl, List.length_cons h2 t2]
          apply Nat.lt_succ_self

        if h1 == h2 then
          have _ : t1.length + t2.length < l1.length + l2.length := by
            apply Nat.add_lt_add
            assumption; assumption

          subaux t1 t2
        else if compare h1 h2 == lt then
          have _ : t1.length + l2.length < l1.length + l2.length := by
            apply Nat.add_lt_add_right
            assumption

          h1 :: subaux t1 l2
        else
          have _ : l1.length + t2.length < l1.length + l2.length := by
            apply Nat.add_lt_add_left
            assumption

          subaux l1 t2
  termination_by l1.length + l2.length

#guard subtract [1,2,3,4] [2,3] == [1,4]
#guard subtract [] [2,3] == []
#guard subtract [2,3] [] == [2,3]

/-- Subset predicate -/
def subset : List α → List α → Bool
  | l1, l2 => aux (setify l1) (setify l2)
where
  aux
    | [], _ => true  -- order matters in the first two match arms
    | _, [] => false
    | l1@(h1 :: t1), h2 :: t2 =>
        if h1 == h2 then
          aux t1 t2
        else if compare h1 h2 == .lt then
          false
        else aux l1 t2

#guard subset [1] [1,2]
#guard subset [1,2] [1,2]
#guard subset [] [1,2]
#guard subset ([] : List Nat) []
#guard not (subset [1,2,3] [1,2])

/-- **Proper** subset -/
def psubset : List α → List α → Bool
  | l1, l2 => p_subaux (setify l1) (setify l2)
where
  p_subaux
    | _, [] => false  -- order matters in the first two match arms
    | [], _ => true
    | l1@(h1 :: t1), h2 :: t2 =>
        if h1 == h2 then
          p_subaux t1 t2
        else if compare h1 h2 == .lt then
          false
        else subset.aux l1 t2  -- note: subset aux in this branch, not psubset aux

#guard psubset [1] [1,2]
#guard not (psubset [1,2] [1,2])
#guard psubset [] [1,2]
#guard not (psubset ([] : List Nat) [])
#guard not (psubset [1,2,3] [1,2])
#guard psubset [1, 2, 3, 4] [1, 5, 2, 3, 4]
#guard not (psubset [1, 5, 2, 3, 4] [1, 2, 3, 4])
#guard psubset ["pc", "nhc", "nlx", "npx"] ["pc", "nhx", "nhc", "nlx", "npx"]
/-
Regression test for `psubset` in the context of subsumption.

[P(c_x), ~H(x, y), ~H(c_x, x), ~L(x), ~P(x)],
[P(c_x), ~H(x, y), ~H(c_x, x), ~P(x), ~R(x)],
[P(c_x), ~H(c_x, x), ~L(x), ~P(x)],
[P(c_x), ~H(c_x, x), ~P(x), ~R(x)]

==>

[P(c_x), ~H(c_x, x), ~L(x), ~P(x)],
[P(c_x), ~H(c_x, x), ~P(x), ~R(x)]
-/
#guard
  let lls := [
    ["pc", "nhx", "nhc", "nlx", "npx"],
    ["pc", "nhx", "nhc", "npx", "nrx"],
    ["pc", "nhc", "nlx", "npx"],
    ["pc", "nhc", "npx", "nrx"],
  ]
  (List.filterTR (fun d => not (List.any lls (fun d' => Set.psubset d' d))) lls).length == 2

def image [BEq β] [Ord β] (f : α → β) (xs: List α) : List β :=
  setify (List.mapTR f xs)

def insert (x: α) (xs: List α) : List α :=
  setify (x :: xs)

end Set


-- #eval (Set.setify (List.all_pairs Set.union
--   ((fun l => [l]) <$> List.range 90)
--   ((fun l => [l]) <$> List.range 7000))).length
