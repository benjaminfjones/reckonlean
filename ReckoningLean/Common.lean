/- `id` is builtin -/
/- composition `**` is backwards pipeline <| -/

namespace List
  /- TODO Do we actually need `end_itlist` ?-/
  def end_itlist [Inhabited α] (f: α → α → α) (l: List α) : α :=
    match l with
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

  def distinct_pairs (l : List α) : List (α × α) :=
    match l with
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

  #eval range_from 1 4
  example : range_from 1 4 = [1, 2, 3, 4] := by
    sorry
    -- simp [range_from]

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

  def non (p : α → Bool) (x: α) : Bool := not (p x)
  example : map (non (fun x => x % 2 = 0)) [0, 1, 2] = [false, true, false] := by rfl

end List