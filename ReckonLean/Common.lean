/- `id` is builtin -/
/- composition `**` is backwards pipeline <| -/

namespace List
  /- TODO Do we actually need `end_itlist` ?-/
  def end_itlist [Inhabited α] (f: α → α → α) : List α → α
    | [] => panic! "end_itlist"
    | [x] => x
    | h :: t => f h (end_itlist f t)

  def all_pairs (f : α → α → β) (l1 l2 : List α) : List β :=
    match l1 with
    | [] => []
    | h1 :: t1 => foldr (fun x a => f h1 x :: a) (all_pairs f t1 l2) l2

  example : all_pairs (fun x y => x + y) [1,2] [-1, -3] =
    [0, -2, 1, -1] := by rfl
  example : all_pairs (fun x y => x * y) [1,2,3] [-1, -2, -3] =
    [-1, -2, -3, -2, -4, -6, -3, -6, -9] := by rfl

  def distinct_pairs : List α -> List (α × α)
    | [] => []
    | x :: t => foldr (fun y a => (x, y) :: a) (distinct_pairs t) t

  example : distinct_pairs [1, 2, 3] = [(1, 2), (1, 3), (2, 3)] := by rfl
  example : distinct_pairs [0, 1] = [(0, 1)] := by rfl
  example : distinct_pairs [0] = [] := by rfl

  /- TODO: prove termination -/
  def range_from (i j: Int) : List Int :=
    if j < i then [] else i :: range_from (i+1) j
  termination_by range_from i j => j - i + 1
  decreasing_by
    sorry
/- Attempt 1 w/ Nat
  decreasing_by
    simp_wf
    have hlt : ¬ j < i := by assumption
    have hle : j ≥ i := Nat.ge_of_not_lt hlt
    have hiplo : i = (i + 1) - 1 := by
      rw [Nat.add_sub_cancel]
    conv =>
      rhs
      rw [hiplo]
    /- ⊢ j - (i + 1) + 1 < j - (i + 1 - 1) + 1 -/
    sorry
-/
/- Attempt 1 w/ Int, no Int lemmas available! -/

  example : range_from 1 4 = [1, 2, 3, 4] := by rfl

  /- A different API that computes the same function, with termination proof! -/
  def range_offset (i : Nat) : Nat → List Nat
    | 0 => []
    | Nat.succ k => i :: range_offset (i+1) k
  termination_by range_offset i k => k
  decreasing_by
    simp_wf
    apply Nat.lt_succ_self

  #eval range_offset 1 4
  example : range_offset 1 4 = [1, 2, 3, 4] := by rfl

  /- A provably terminating version of `range_from` whose definitional equality
     works out conveniently! -/
  def range_from' (i j: Int) : List Int :=
    if j < i then [] else map (fun x => Int.ofNat x + i) $ range_offset 0 (j-i+1).natAbs

  example : range_from' 1 4 = [1, 2, 3, 4] := by rfl
  example : range_from' 1 4 = [1, 2, 3, 4] := by rfl

  def non (p : α → Bool) (x: α) : Bool := not (p x)
  example : map (non (fun x => x % 2 = 0)) [0, 1, 2] = [false, true, false] := by rfl

end List

/-
Sets as sorted lists

This implementation is used in order not to have to depend on Std4 or Mathlib4
for a set datatype. It is fast enough the purposes of this project.
-/

/-

Useful vim macros

:s/(\*/\/-/g
:s/\*)/-\//g
:s/^let /def /g
:s/=/:=/g
:s/ in$//g
:s/->/=>/g

-/ -/ -/ -/
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

/- Most of the set functions use the `.isLE` method of Ordering -/
#check (compare 1 2).isLE

/- Merging of sorted lists (maintaining repetitions) -/
def merge(l1 l2: List α) : List α :=
  match l1 with
  | [] => l2
  | h1 :: t1 => (
      match l2 with
      | [] => l1
      | h2 :: t2 =>
          if (compare h1 h2).isLE then h1 :: merge t1 l2 else h2 :: merge l1 t2)
termination_by merge l1 l2 => l1.length + l2.length
decreasing_by
  simp_wf
  sorry

#eval merge [] [1,2] == [1, 2]  -- true
#eval merge [5] [1,2] == [1, 2, 5]  -- true
#eval merge [1,2] [1,3] == [1, 1, 2, 3]  -- true


/- Bottom-up mergesort -/
def sort : List α → List α :=
  let rec mergepairs l1 l2 :=
    match (l1, l2) with
    | (s::[], []) => s
    | (l, []) => mergepairs [] l
    | (l, [ s1 ]) => mergepairs (s1 :: l) []
    | (l, s1 :: s2 :: ss) => mergepairs (merge s1 s2 :: l) ss
  fun
    | [] => []
    | l => mergepairs [] ((fun x => [ x ]) <$> l)
termination_by _ => 0
decreasing_by
  simp_wf
  sorry

#eval sort [4, 3, 2, 1] == [1, 2, 3, 4]  -- true
#eval sort [1, 3, 2, 1] == [1, 1, 2, 3]  -- true
#eval sort [1] == [1]  -- true

/- Construct a set, represented as a canonical list -/
def setify :=
  let rec canonical (lis: List α) :=
    match lis with
    | x :: rest@(y :: _) => compare x y == lt && canonical rest
    | _ => true
  fun l =>
    if canonical l then l
    else
      uniq <| sort l

#eval setify [1, 3, 2, 1] == [1, 2, 3]  -- true

/- Construct the union of two lists, as a canonical set -/
def union : List α → List α → List α
  | s1, s2 => aux_union (setify s1) (setify s2)
where
  aux_union l1 l2 :=
    match (l1, l2) with
    | ([], l2) => l2
    | (l1, []) => l1
    | (l1@(h1 :: t1), l2@(h2 :: t2)) =>
        if h1 == h2 then h1 :: aux_union t1 t2
        else if compare h1 h2 == lt then h1 :: aux_union t1 l2
        else h2 :: aux_union l1 t2
  decreasing_by sorry  -- same as the proof for `intersect.aux`

#eval union [1,2,3] [4,5]  -- [1, 2, 3, 4, 5]
#eval union [1,2,3] [1, 2, 3]  -- [1, 2, 3]

/- Return a list of all subsets of given size. -/
/- TODO: Need Ord (List α)
def allsubsets (size: Int) (set: List α) : List (List α) :=
  let set := setify set
  if size <= 0 then [ [] ]
  else if size > List.length set then []
  else (
      match set with
      | [] => []
      | s :: rest =>
          union
            (List.map (union [ s ]) (allsubsets (size - 1) rest))
            (allsubsets size rest))
-/

/-
Setify the input lists and return their intersection.

The termination proof for `intersect` and its recursive helper `aux`
is carried out below for the fun of it.
-/
def intersect (l1 l2: List α) : List α :=
  aux (setify l1) (setify l2)
where
  aux
    | [], _ => []
    | _, [] => []
    | l1@(h1 :: t1), l2@(h2 :: t2) =>
        have _ : sizeOf t1 < 1 + sizeOf t1 := by simp_arith
        have _ : sizeOf t2 < 1 + sizeOf t2 := by simp_arith
        have _ : sizeOf t1 < sizeOf l1 := by simp [*]
        have _ : sizeOf t2 < sizeOf l2 := by simp [*]
        if h1 == h2 then
          have _ : sizeOf t1 + sizeOf t2 < 1 + sizeOf t1 + (1 + sizeOf t2) := by simp_arith
          h1 :: aux t1 t2
        else
          if compare h1 h2 == lt then
            have _ : sizeOf t1 + sizeOf l2 < 1 + sizeOf t1 + sizeOf l2 := by simp_arith
            aux t1 l2
          else
            have _ : sizeOf l1 + sizeOf t2 < sizeOf l1 + (1 + sizeOf t2) := by simp_arith
            aux l1 t2
  termination_by aux l1 l2 => sizeOf l1 + sizeOf l2
  decreasing_by
    /- unfold definitions about well-founded relations -/
    simp_wf
    /- apply the high-power simplifies once all the `have` hypotheses are
       in scope. Each of the simultaneously focused goals produced by
       `decreasing_by` is then solved by assumption -/
    simp_all

#eval intersect [1,2,3] [4,5]     -- []
#eval intersect [1,2,3] [3, 4,5]  -- [3]
#eval union [1,2,3] [1, 2, 3]     -- [1, 2, 3]

/- Remove a set from another -/
def subtract : List α → List α → List α
  | s1, s2 => subaux (setify s1) (setify s2)
where
  subaux
    | [], _ => []
    | l1, [] => l1
    | l1@(h1 :: t1), l2@(h2 :: t2) =>
        if h1 == h2 then subaux t1 t2
        else if compare h1 h2 == lt then h1 :: subaux t1 l2
        else subaux l1 t2
  decreasing_by sorry  /- see proof for `intersect` -/

/- Strict subset predicate -/
def subset : List α → List α → Bool
  | l1, l2 => aux (setify l1) (setify l2)
where
  aux
    | _, [] => false  -- order matters in the first two match arms
    | [], _ => true
    | l1@(h1 :: t1), h2 :: t2 =>
        if h1 == h2 then
          aux t1 t2
        else if compare h1 h2 == .lt then
          false
        else aux l1 t2

/- Partial subset -/
def psubset : List α → List α → Bool
  | l1, l2 => aux (setify l1) (setify l2)
where
  aux
    | _, [] => false
    | [], _ => true
    | l1@(h1 :: t1), h2 :: t2 =>
        if h1 == h2 then
          aux t1 t2
        else if compare h1 h2 == lt then
          false
        else aux l1 t2

def unions (s: List (List α)) : List α := setify (List.foldl List.append [] s)

#eval unions [[1,2,3], [4,5,6], [1,5,8]] == [1,2,3,4,5,6,8]  -- true

def set_image {β: Type} [Ord β] [BEq β] (f: α → β) (s: List α) : List β :=
  setify (List.map f s)
