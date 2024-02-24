import ReckonLean.Common
import ReckonLean.FPF
import ReckonLean.Prop

/-!
Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures
-/

abbrev PCNFFormula := List (List (Formula Prp))

/- ------------------------------------------------------------------------- -/
/- The Davis-Putnam procedure.                                               -/
/- ------------------------------------------------------------------------- -/

def one_literal_rule (clauses : PCNFFormula) : Option PCNFFormula :=
  Option.map (unit_prop clauses) (List.find? (fun cl => List.length cl == 1) clauses)
where
  unit_prop (clauses: PCNFFormula) (pcl: List (Formula Prp)) : PCNFFormula :=
    let u := List.head! pcl
    -- dbg_trace "unit_prop: {print_pf u}"
    let u' := negate u
    let clauses' := List.filter (fun cl => not (List.mem u cl)) clauses
    Set.set_image (fun cl => Set.subtract cl [ u' ]) clauses'

def affirmative_negative_rule (clauses : PCNFFormula) : Option PCNFFormula :=
  let lits := Set.unions clauses
  let (neg', pos) := List.partition negative lits
  let neg := Set.set_image negate neg'
  /- find lits that only appear positively or only appear negatively -/
  let pos_only := Set.subtract pos neg
  -- dbg_trace "anr: pos_only #{pos_only.length}"
  let neg_only := Set.subtract neg pos
  -- dbg_trace "anr: neg_only #{neg_only.length}"
  let pure := Set.union pos_only (Set.set_image negate neg_only)
  if pure == [] then none
  else some (List.filter (fun cl => Set.intersect cl pure == []) clauses)

/- Resolve the formula on a literal `p` -/
def resolve_on (lit : Formula Prp) (clauses : PCNFFormula) : PCNFFormula :=
  -- dbg_trace "resolve_on: {print_pf lit}"
  let lit' := negate lit
  let (pos, notpos) := List.partition (List.mem lit) clauses
  let (neg, other) := List.partition (List.mem lit') notpos
  let pos' := Set.set_image (List.filterTR (· != lit)) pos
  let neg' := Set.set_image (List.filterTR (· != lit')) neg
  -- Note: `res0` is worst case quadratic in the #clauses
  let res0 := List.all_pairs Set.union pos' neg'
  let non_trivs := List.filterTR (non CNF.trivial) res0
  -- Note: Set.unions is very much not tail recursive
  --- dbg_trace s!"resolve_on: union of {other.length} and {non_trivs.length}"
  Set.union other non_trivs

/- Heuristic for determing how large the formula blow-up is when applying
   `resolve_on` to a given literal. -/
def resolution_blowup (cls : PCNFFormula) (l : Formula Prp) : Int :=
  let m := List.length (List.filterTR (List.mem l) cls)
  let n := List.length (List.filterTR (List.mem (negate l)) cls)
  (m * n) - m - n

/- Apply `resolve_on` for the best literal according to heuristics -/
def resolution_rule (clauses: PCNFFormula) : Option PCNFFormula :=
  -- dbg_trace s!"resolution_rule: #clauses {clauses.length}"
  let pvs := List.filterTR positive (Set.unions clauses)
  Option.map (fun p => resolve_on p clauses)
    (List.minimize (resolution_blowup clauses) pvs)

/- ------------------------------------------------------------------------- -/
/- Overall procedure.                                                        -/
/- ------------------------------------------------------------------------- -/

partial def dp (clauses: PCNFFormula) : Bool :=
  -- dbg_trace s!"dp: #clauses {List.length clauses}"
  if clauses == [] then true
  else if List.mem [] clauses then false
  else
    /- apply `one_literal_rule` until it returns `none` -/
    if let some res := Option.map dp (one_literal_rule clauses) then
      res
    else
      /- `one_literal_rule` doesn't apply any further -/
      /- apply `affirmative_negative_rule` until it returns `none` -/
      if let some res := Option.map dp (affirmative_negative_rule clauses) then
        res
      else
        /- `affirmative_negative_rule` doesn't apply any further -/
        /- apply `resolution_rule` and recurse -/
        dp (resolution_rule clauses).get!
-- termination_by dp clauses => clauses.length  -- need lemmas about rules

/- ------------------------------------------------------------------------- -/
/- Davis-Putnam satisfiability tester and tautology checker.                 -/
/- ------------------------------------------------------------------------- -/

def dpsat fm := dp (CNF.defcnf_opt_sets fm)
def dptaut fm := not (dpsat (.Not fm))


/- ------------------------------------------------------------------------- -/
/- The Davis-Putnam-Logemann-Loveland procedure.                             -/
/- ------------------------------------------------------------------------- -/

/- Count occurances of a literal or its negation in the formula -/
def posneg_count (clauses: PCNFFormula) (lit: PFormula) : Nat :=
  let lit' := negate lit
  let m := List.length (List.filterTR (fun cl => List.mem lit cl) clauses)
  let n := List.length (List.filterTR (fun cl => List.mem lit' cl) clauses)
  m + n

/- DPPL: naive recursive version -/
partial def dpll (clauses: PCNFFormula) : Bool :=
  -- dbg_trace s!"dp: #clauses {List.length clauses}"
  if clauses == [] then true
  else if List.mem [] clauses then false
  else
    if let some res := Option.map dpll (one_literal_rule clauses) then
      res
    else
      if let some res := Option.map dpll (affirmative_negative_rule clauses) then
        res
      else
        /- apply splitting rule and recurse -/
        let pvs := List.filterTR positive (Set.unions clauses)
        let p := (List.maximize (posneg_count clauses) pvs).get!
        (dpll ([p] :: clauses)) || (dpll ([negate p] :: clauses))
-- termination_by number of atoms

def dpllsat (fm: PFormula) := dpll (CNF.defcnf_opt_sets fm)
def dplltaut (fm: PFormula) := not (dpllsat (.Not fm))


/- ------------------------------------------------------------------------- -/
/- The **Iterative** Davis-Putnam-Logemann-Loveland procedure.               -/
/- ------------------------------------------------------------------------- -/

open FPF

inductive LitState where
  | Guessed
  | Deduced
deriving Repr, BEq

structure Decision where
  literal: PFormula
  decision: LitState
deriving Repr

instance : ToString Decision where
  toString d :=
    let marker := if d.decision == .Guessed then "|" else ""
    s!"{marker}{print_qliteral print_prp d.literal}"

abbrev Trail := List Decision

def unassigned (clauses: PCNFFormula) (trail: Trail) : List PFormula :=
  Set.subtract all_vars dec_vars
where
  all_vars := Set.unions (Set.image (Set.image litabs) clauses)
  dec_vars := Set.image (litabs ∘ Decision.literal) trail

structure UnitPropState where
  clauses: PCNFFormula
  lookup: Func PFormula Unit
  trail: Trail

/- Apply unit propagation iteratively until reaching a fixpoint -/
partial def unit_subpropagate (msg: String := "") (st: UnitPropState) : UnitPropState :=
  -- filter the negation of defined literals out of current clauses
  let clauses' := List.mapTR (List.filterTR (not ∘ (defined st.lookup) ∘ negate)) st.clauses
  let newu : List PFormula → Option (List PFormula)
    | [c] => if not (defined st.lookup c) then some [c] else none
    | _ => none
  match Set.unions (List.filterMap newu clauses') with
  | [] => {st with clauses := clauses'}
  | us =>
    -- set all new units to Deduced
    -- dbg_trace s!"{msg}: unit_prop: deduced new units = {List.map (print_qliteral print_prp) us}"
    let trail' := List.foldl (fun t p => {literal := p, decision := .Deduced} :: t) st.trail us
    -- define all new units in the lookup
    let lookup' := List.foldl (fun l u => (u |-> ()) l) st.lookup us
    unit_subpropagate msg {clauses := clauses', lookup := lookup', trail := trail'}

def unit_propagate (msg: String := "") (st: UnitPropState) : UnitPropState :=
  let current_lookup := List.foldl (fun lk d => (d.literal |-> ()) lk) undefined st.trail
  let st' := unit_subpropagate msg {st with lookup := current_lookup}
  -- current_lookup is only used in the subpropagate function
  {st' with lookup := undefined}

/- Backtrack to the last `Guessed` literal -/
def backtrack : Trail → Trail
  | [] => []
  | trail@(d :: ds) => if d.decision == .Deduced then backtrack ds else trail

/- `backtrack` is monotonically decreasing -/
theorem length_backtrack : ∀ tr : Trail,
  List.length (backtrack tr) ≤ List.length tr := by
    intro t
    induction t with
    | nil => unfold backtrack; apply Nat.le_refl
    | cons d ds ih =>
      simp [backtrack]
      cases d.decision == .Deduced
      . simp
      . simp; apply Nat.le_succ_of_le; assumption

partial def dpli_aux (clauses: PCNFFormula) (trail: Trail) : Bool :=
  let st := unit_propagate "dpli" {clauses, lookup := undefined, trail}
  if List.mem [] st.clauses then
    match backtrack trail with
    | [] => false
    | d :: ds => if d.decision == .Guessed then
        dpli_aux clauses ({literal := negate d.literal, decision := .Deduced} :: ds)
      else
        -- this is unreachable due to how `backtrack` is implemented and the `[]` case above
        false
  else
    match unassigned clauses st.trail with
    | [] => true  -- SAT!  TODO: extract a satisfying assignment
    | ls =>
        let l := (List.maximize (posneg_count st.clauses) ls).get!  -- `ls` is non-empty
        dpli_aux clauses ({literal := l, decision := .Guessed} :: st.trail)

def dpli (clauses: PCNFFormula) : Bool :=
  dpli_aux clauses []

def dplisat := dpli ∘ CNF.defcnf_opt_sets
def dplitaut := not ∘ dplisat ∘ (.Not ·)

def ex1 := <<"(p ∨ q ∧ r) ∧ (~p ∨ ~r)">>
/-
["p", "p_1"]
["p_1", "~q", "~r"]
["q", "~p_1"]
["r", "~p_1"]
["~p", "~r"]

dpli: decide p_1
unit_prop: deduced = [[q, r]]
unit_prop: deduced = [[~p]]
-/
#guard dplisat ex1

-- from https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
def ex2 := <<"(x1 ∨ x4) ∧ (x1 ∨ ~x3 ∨ ~x8) ∧ (x1 ∨ x8 ∨ x12) ∧ (x2 ∨ x11) ∧ (~x7 ∨ ~x3 ∨ x9) ∧ (~x7 ∨ x8 ∨ ~x9) ∧ (x7 ∨ x8 ∨ ~x10) ∧ (x7 ∨ x10 ∨ ~x12)">>
#guard dplisat ex2
#guard not (dplitaut ex2)


/- ------------------------------------------------------------------------- -/
/- The Backjumping, clause learning DPLL procedure                           -/
/- ------------------------------------------------------------------------- -/

/-!
Backjump to the most recent decision that still leads to a conflict.

Note: `p` is a literal assumed to occur in the trail before the most recent decision
to try backjumping to.

Termination is proved using a monotonicity theorem about `backtrack`
-/
def backjump (clauses: PCNFFormula) (p: PFormula) (trail: Trail) : Trail :=
  match hbt : backtrack trail with  -- naming hypothesis `hbt` puts the match branch assumptions in context
  | {literal := _, decision := .Guessed} :: tt =>
    -- fact to use in termination proof
    have _ : List.length (backtrack trail) ≤ List.length trail := length_backtrack trail
    -- backtrack to the most recent guess, replace it with `p`, and propagate
    let st := unit_propagate "bj" {clauses, lookup := undefined, trail := {literal := p, decision := .Guessed} :: tt}
    -- if we still have a conflict recurse, otherwise `d` was sufficient to cause a conflict
    if List.mem [] st.clauses then
      -- BEGIN fact to use in termination proof
      have _ : List.length tt < List.length trail := by
        simp_all
        apply Nat.lt_of_succ_le; assumption
      -- END
      backjump clauses p tt
    else
      trail
  | _ => trail
termination_by backjump _ _ tr => tr.length
decreasing_by
  simp_wf
  assumption  -- WOOT

partial def dplb_aux (learn: Bool) (clauses: PCNFFormula) (trail: Trail) : Bool :=
  -- dbg_trace s!"====\ndplb: starting trail = {trail}"
  let st := unit_propagate "dplb" {clauses, lookup := undefined, trail}
  -- conflict
  if List.mem [] st.clauses then
    -- dbg_trace s!"dplb: deduced a conflict, starting backjump"
    match backtrack trail with
    | {literal := p, decision := .Guessed} :: tt =>
      -- backjump to the most recent decision literal that entails a conflict
      let trail' := backjump clauses p tt
      -- dbg_trace s!"dplb: backjump to {trail'}"
      -- dbg_trace s!"dplb: backtrack distance = {trail.length - (backtrack trail).length}"
      -- dbg_trace s!"dplb: backjump distance = {trail.length - trail'.length - 1}"
      -- gather all decision literals { d1 ... dn } up to the backjumped point
      if (trail'.length + 1) == (backtrack trail).length || not learn then
        dplb_aux learn clauses ({literal := negate p, decision := .Deduced} :: trail')
      else
        let declits := List.filter (fun {literal := _, decision := d} => d == .Guessed) trail'
        -- learned conflict clause is (¬ p ∨ ¬ d1 ∨ ... ∨ ¬ dn)
        let conflict := Set.insert (negate p) (Set.image (negate ∘ (·.literal)) declits)
        -- dbg_trace s!"dplb: |bt trail| = {(backtrack trail).length}"
        -- dbg_trace s!"dplb: |conflict clause| = {conflict.length}"
        -- dbg_trace s!"dplb: conflict: {CNF.print_cnf_formula_sets [conflict]}"
        -- dbg_trace s!"dplb: deduce {print_pf (negate p)}"
        dplb_aux learn (conflict :: clauses) ({literal := negate p, decision := .Deduced} :: trail')
    | _ => false  -- really only [], since backtrack either returns [] or a list with head Guessed
  else
    -- dbg_trace s!"dplb: deduce new trail {st.trail}"
    match unassigned clauses st.trail with
    | [] => true  -- TODO: return a model
    | ls => let l := (List.maximize (posneg_count st.clauses) ls).get!  -- ls is non-empty
            dplb_aux learn clauses ({literal := l, decision := .Guessed} :: st.trail)
    -- uncomment to use trivial decision literal selection
    -- | l :: _ =>
      -- dbg_trace s!"dplb: guess {print_pf l}"
      -- dplb_aux clauses ({literal := l, decision := .Guessed} :: st.trail)
-- termination_by length of {unassigned literals in trail}

/- DPLL with backjumping without clause learning -/
def dplb (clauses: PCNFFormula) : Bool :=
  dplb_aux false clauses []

def dplbsat := dplb ∘ CNF.defcnf_opt_sets
def dplbtaut := not ∘ dplbsat ∘ (.Not ·)

/- DPLL with backjumping and simple clause learning -/
def dplb' (clauses: PCNFFormula) : Bool :=
  dplb_aux true clauses []

def dplb'sat := dplb' ∘ CNF.defcnf_opt_sets
def dplb'taut := not ∘ dplb'sat ∘ (.Not ·)

-- Running example from the Handbook
-- `formula := (~p1 ∨ ~p10 ∨ p11) ∧ (~p1 ∨ ~p10 ∨ ~p11)`
--
-- suppose we've guessed `true` for p1 ... p10 and then applied unit_prop:
-- unit_prop ==> (p11) ∧ (~p11)
-- unit_prop ==> xxx conflict
-- backtrack ==> trail: p1 ... p10, let `p := p10`, `tt := p1 ... p9`
-- backjump formula p10 [p1 ... p9]
--   * backtrack [p1 ... p9] ==> p1 ... p9 (unchanged)
--   * unit_prop [p1 ... p8 p10] ==> (p11) ∧ (~p11)`
--                               ==> xxx conflict
--                               ==> recurse backjump formula p10 [p1 ... p8]
--   * eventually get to: backjump formula p10 [p1]
--      ==> unit_prop [p10]  ==> no conflict ==> return [p1]
-- declits := [p1]
-- conflict := [~p1, ~p10]
-- recurse dplb

-- w is p10, z is p11 in above example
def p1p10_ex :=
  <<"(~p1 ∨ ~w ∨ z) ∧ (~p1 ∨ ~w ∨ ~z) ∧ (p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ p8 ∨ p9)">>
/-
A gory and completely unneccessary debug trace for p1p10_ex. The trace was generated
using a completely trivial decision literal selection which forces deciding p1, p2, ...
p9, p10 in order, then backjumping to p1, etc.

====
dplb: starting trail = []
dplb: deduce new trail []
dplb: guess <<p1>>
====
dplb: starting trail = [|p1]
dplb: deduce new trail [|p1]
dplb: guess <<p2>>
====
dplb: starting trail = [|p2, |p1]
dplb: deduce new trail [|p2, |p1]
dplb: guess <<p3>>
====
dplb: starting trail = [|p3, |p2, |p1]
dplb: deduce new trail [|p3, |p2, |p1]
dplb: guess <<p4>>
====
dplb: starting trail = [|p4, |p3, |p2, |p1]
dplb: deduce new trail [|p4, |p3, |p2, |p1]
dplb: guess <<p5>>
====
dplb: starting trail = [|p5, |p4, |p3, |p2, |p1]
dplb: deduce new trail [|p5, |p4, |p3, |p2, |p1]
dplb: guess <<p6>>
====
dplb: starting trail = [|p6, |p5, |p4, |p3, |p2, |p1]
dplb: deduce new trail [|p6, |p5, |p4, |p3, |p2, |p1]
dplb: guess <<p7>>
====
dplb: starting trail = [|p7, |p6, |p5, |p4, |p3, |p2, |p1]
dplb: deduce new trail [|p7, |p6, |p5, |p4, |p3, |p2, |p1]
dplb: guess <<p8>>
====
dplb: starting trail = [|p8, |p7, |p6, |p5, |p4, |p3, |p2, |p1]
dplb: deduce new trail [|p8, |p7, |p6, |p5, |p4, |p3, |p2, |p1]
dplb: guess <<p9>>
====
dplb: starting trail = [|p9, |p8, |p7, |p6, |p5, |p4, |p3, |p2, |p1]
dplb: deduce new trail [|p9, |p8, |p7, |p6, |p5, |p4, |p3, |p2, |p1]
dplb: guess <<w>>
====
dplb: starting trail = [|w, |p9, |p8, |p7, |p6, |p5, |p4, |p3, |p2, |p1]
dplb: unit_prop: deduced new units = [z, ~z]
bj: try deducing conflict from [|w, |p8, |p7, |p6, |p5, |p4, |p3, |p2, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w, |p7, |p6, |p5, |p4, |p3, |p2, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w, |p6, |p5, |p4, |p3, |p2, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w, |p5, |p4, |p3, |p2, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w, |p4, |p3, |p2, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w, |p3, |p2, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w, |p2, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w, |p1]
bj: unit_prop: deduced new units = [z, ~z]
bj: found conflict!
bj: try deducing conflict from [|w]
bj: no conflict!
bj: # decision jumps 8
dplb: backjump to [|p1]
dplb: backtrack distance = 0
dplb: backjump distance = 8
dplb: |bt trail| = 10
dplb: |conflict clause| = 2
dplb: conflict: [[~p1, ~w]]
dplb: deduce <<~w>>
====
dplb: starting trail = [~w, |p1]
dplb: deduce new trail [~w, |p1]
dplb: guess <<p2>>
====
dplb: starting trail = [|p2, ~w, |p1]
dplb: deduce new trail [|p2, ~w, |p1]
dplb: guess <<p3>>
====
dplb: starting trail = [|p3, |p2, ~w, |p1]
dplb: deduce new trail [|p3, |p2, ~w, |p1]
dplb: guess <<p4>>
====
dplb: starting trail = [|p4, |p3, |p2, ~w, |p1]
dplb: deduce new trail [|p4, |p3, |p2, ~w, |p1]
dplb: guess <<p5>>
====
dplb: starting trail = [|p5, |p4, |p3, |p2, ~w, |p1]
dplb: deduce new trail [|p5, |p4, |p3, |p2, ~w, |p1]
dplb: guess <<p6>>
====
dplb: starting trail = [|p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: deduce new trail [|p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: guess <<p7>>
====
dplb: starting trail = [|p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: deduce new trail [|p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: guess <<p8>>
====
dplb: starting trail = [|p8, |p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: deduce new trail [|p8, |p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: guess <<p9>>
====
dplb: starting trail = [|p9, |p8, |p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: deduce new trail [|p9, |p8, |p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: guess <<z>>
====
dplb: starting trail = [|z, |p9, |p8, |p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]
dplb: deduce new trail [|z, |p9, |p8, |p7, |p6, |p5, |p4, |p3, |p2, ~w, |p1]

-/
#guard dplbsat p1p10_ex

-- from https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
#guard dplbsat ex2
#guard not (dplbtaut ex2)


/- ========================================================================= -/
/- EXAMPLES                                                                  -/
/- ========================================================================= -/

namespace Examples

/- Alises just for this section -/
def satisfiable := dpsat
def tautology := dplitaut

/- Simple equivalence proof for `nnf` and `nenf` from Prop -/
def iff_ex := <<"(p <=> q) <=> ~(r ==> s)">>
/- Prove fm <=> NNF <=> NENF -/
#guard dptaut (.Iff iff_ex (nnf iff_ex))
#guard dptaut (.Iff iff_ex (nenf iff_ex))
/- Prove defcnf_opt fm => fm -/
#guard dptaut (.Imp (CNF.defcnf_opt iff_ex) iff_ex)
#guard dplltaut (.Imp (CNF.defcnf_opt iff_ex) iff_ex)

/- ------------------- -/
/- Lots of tautologies -/
/- ------------------- -/

/- "tautology: and_comm" -/
#guard dptaut <<"p ∧ q <=> q ∧ p">>
#guard dplltaut <<"p ∧ q <=> q ∧ p">>

/- Extended example where DP requires several resolution steps -/
section pqqr
  def pqqr := <<"p ∧ q <=> q ∧ r">>
  def not_pqqr := <<"~(p ∧ q <=> q ∧ r)">>

  /- NNF is correct -/
  #guard print_pf (nnf not_pqqr)
    == "<<(p ∧ q) ∧ (~q ∨ ~r) ∨ (~p ∨ ~q) ∧ q ∧ r>>"
  /-
  clearly: p, q, ~r satisfies the defcnf of `not_pqqr`
  [[ p,  q],
   [ p,  r],
   [ q],
   [ ~p,  ~q, ~r]]
  -/
  #guard CNF.print_cnf_formula_sets (CNF.simpcnf not_pqqr) ==
    [["p", "r"], ["q"], ["~p", "~q", "~r"]]
    -- a bug where subsumption was not effective led to:
    -- [["p", "q"], ["p", "r"], ["q"], ["~p", "~q", "~r"]]
    -- which has a redundant first clause

  /-
  DP trace:
  - unit_prop: <<p_3>>
  - resolve_on: <<p>>
  - resolve_on: <<p_1>>
  - resolve_on: <<r>>
  - afr: pos_only #1
  - arf: neg_only #0
  SAT
  -/
  #guard satisfiable not_pqqr
  #guard not (tautology pqqr)
  /- related equivalence proofs -/
  /- By DP -/
  #guard dptaut (Formula.Iff (nenf not_pqqr) (nnf not_pqqr))
  #guard dptaut (Formula.Iff (not_pqqr) (nnf not_pqqr))
  #guard not (dptaut (Formula.Iff (pqqr) (nnf not_pqqr)))
  /- By DPLL -/
  #guard dplltaut (Formula.Iff (nenf not_pqqr) (nnf not_pqqr))
  #guard dplltaut (Formula.Iff (not_pqqr) (nnf not_pqqr))
  #guard not (dplltaut (Formula.Iff (pqqr) (nnf not_pqqr)))
end pqqr

/- "tautology: p or not p" -/
#guard tautology <<"p ∨ ~p">>

/- "not tautology: p or q implies p" -/
#guard not (tautology <<"p ∨ q ==> p">>)

/- "tautology: p or q implies stuff"; uses only unit propagation -/
#guard not (tautology <<"p ∨ q ==> q ∨ (p <=> q)">>)

/- "satisfiable: p or q implies stuff"; uses afr and resolution -/
#guard satisfiable <<"p ∨ q ==> q ∨ (p <=> q)">>

/- "tautology: p or q and not (p and q)" -/
#guard tautology <<"(p ∨ q) ∧ ~(p ∧ q) ==> (~p <=> q)">>

/- Surprising tautologies, including Dijkstra's Golden Rule -/

/- "tautology: counter intuitive" -/
#guard tautology <<"(p ==> q) ∨ (q ==> p)">>

/- "tautology: Dijkstra Scholten"

DP trace:
- unit_prop: <<p_6>>
- resolve_on: <<p_2>>
- resolve_on: <<p>>
- resolve_on: <<p_1>>
- resolve_on: <<r>>
- resolve_on: <<q>>
- resolve_on: <<p_3>>
- resolve_on: <<p_4>>
- unit_prop: <<p_5>>
-/
#guard tautology <<"p ∨ (q <=> r) <=> (p ∨ q <=> p ∨ r)">>

/- "Golden Rule" -/
/- "tautology: golden rule 1" -/
#guard tautology <<"p ∧ q <=> ((p <=> q) <=> p ∨ q)">>

/- "tautology: contrapositive 1" -/
#guard tautology <<"(p ==> q) <=> (~q ==> ~p)">>

/- "tautology: contrapositive 2" -/
#guard tautology <<"(p ==> ~q) <=> (q ==> ~p)">>

/- "common fallacy: implies not symmetric" -/
#guard not (tautology <<"(p ==> q) <=> (q ==> p)">>)

/- Some logical equivalences allowing elimination of connectives -/

/- "eliminate logical connectives: {==>, false} are adequate" -/
#guard List.all (List.map tautology
  [
    <<"true <=> false ==> false">>,
    <<"~p <=> p ==> false">>,
    <<"p ∧ q <=> (p ==> q ==> false) ==> false">>,
    <<"p ∨ q <=> (p ==> false) ==> q">>,
    <<"(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false">>
  ]) id

/- "montonicity of and"; uses only unit propagation -/
#guard tautology <<"(p ==> p') ∧ (q ==> q') ==> ((p ∧ q) ==> (p' ∧ q'))">>

/- "montonicity of or"; uses only unit propagation -/
#guard tautology <<"(p ==> p') ∧ (q ==> q') ==> ((p ∨ q) ==> (p' ∨ q'))">>

/- Big list of tautologies tested on all implementations -/

def list_o_tautologies : List PFormula := [
  <<"p ∨ ~p">>,
  <<"(p ∨ q) ∧ ~(p ∧ q) ==> (~p <=> q)">>,
  <<"(p ==> q) ∨ (q ==> p)">>,
  <<"p ∨ (q <=> r) <=> (p ∨ q <=> p ∨ r)">>,
  <<"p ∧ q <=> ((p <=> q) <=> p ∨ q)">>,
  <<"(p ==> q) <=> (~q ==> ~p)">>,
  <<"(p ==> ~q) <=> (q ==> ~p)">>,
  <<"true <=> false ==> false">>,
  <<"~p <=> p ==> false">>,
  <<"p ∧ q <=> (p ==> q ==> false) ==> false">>,
  <<"p ∨ q <=> (p ==> false) ==> q">>,
  <<"(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false">>,
  <<"(p ==> p') ∧ (q ==> q') ==> ((p ∧ q) ==> (p' ∧ q'))">>,
  <<"(p ==> p') ∧ (q ==> q') ==> ((p ∨ q) ==> (p' ∨ q'))">>
]

/- Verify all tautologies using DP: in #eval 0.00029 s -/
#guard List.all (List.map dptaut list_o_tautologies) id
/- Verify all tautologies using DPLL; in #eval 0.000125 s -/
#guard List.all (List.map dplltaut list_o_tautologies) id
/- Verify all tautologies using iterative DPLL; in #eval 0.00029 s -/
#guard List.all (List.map dplitaut list_o_tautologies) id
/- Verify all tautologies using backjumping DPLL; in #eval 0.00025 s -/
#guard List.all (List.map dplbtaut list_o_tautologies) id

-- #eval timeit "" $ pure (List.all (List.map dplbtaut list_o_tautologies) id)

end Examples
