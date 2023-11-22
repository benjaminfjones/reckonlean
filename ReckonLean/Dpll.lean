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

def dp (clauses: PCNFFormula) : Bool :=
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
decreasing_by sorry

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
def dpll (clauses: PCNFFormula) : Bool :=
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
decreasing_by sorry

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

-- XXX debug
instance : ToString Decision where
  toString := reprStr

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
def unit_subpropagate (st: UnitPropState) : UnitPropState :=
  -- filter the negation of defined literals out of current clauses
  let clauses' := List.mapTR (List.filterTR (not ∘ (defined st.lookup) ∘ negate)) st.clauses
  let newu : List PFormula → Option (List PFormula)
    | [c] => if not (defined st.lookup c) then some [c] else none
    | _ => none
  match Set.unions (List.filterMap newu clauses') with
  | [] => {st with clauses := clauses'}
  | us =>
    -- set all new units to Deduced
    let trail' := List.foldl (fun t p => {literal := p, decision := .Deduced} :: t) st.trail us
    -- define all new units in the lookup
    let lookup' := List.foldl (fun l u => (u |-> ()) l) st.lookup us
    unit_subpropagate {clauses := clauses', lookup := lookup', trail := trail'}
decreasing_by sorry

def unit_propagate (st: UnitPropState) : UnitPropState :=
  let current_lookup := List.foldl (fun lk d => (d.literal |-> ()) lk) undefined st.trail
  let st' := unit_subpropagate {st with lookup := current_lookup}
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
    | nil => simp
    | cons d ds ih =>
      simp [backtrack]
      cases d.decision <;> simp [backtrack] <;> try (apply Nat.le_succ_of_le; assumption)

def dpli_aux (clauses: PCNFFormula) (trail: Trail) : Bool :=
  let st := unit_propagate {clauses, lookup := undefined, trail}
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
decreasing_by sorry

def dpli (clauses: PCNFFormula) : Bool :=
  dpli_aux clauses []

def dplisat := dpli ∘ CNF.defcnf_opt_sets
def dplitaut := not ∘ dplisat ∘ (.Not ·)


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
    let st := unit_propagate
      {clauses, lookup := undefined, trail := {literal := p, decision := .Guessed} :: tt}
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

def dplb_aux (clauses: PCNFFormula) (trail: Trail) : Bool :=
  let st := unit_propagate {clauses, lookup := undefined, trail}
  -- conflict
  if List.mem [] st.clauses then
    match backtrack trail with
    | {literal := p, decision := .Guessed} :: tt =>
      -- backjump to the most recent decision literal that entails a conflict
      let trail' := backjump clauses p tt
      -- gather all decision literals { d1 ... dn } up to the backjumped point
      let declits := List.filter (fun {literal := _, decision := d} => d == .Guessed) trail'
      -- learned conflict clause is (¬ p ∨ ¬ d1 ∨ ... ∨ ¬ dn)
      -- let conflict := Set.insert (negate p) (Set.image (negate ∘ (·.literal)) declits)
      let conflict := (negate p) :: (List.map (negate ∘ (·.literal)) declits)
      -- dbg_trace s!"conflict: {CNF.print_cnf_formula_sets [conflict]}"
      -- dplb_aux (conflict :: clauses) ({literal := negate p, decision := .Deduced} :: trail')
      dplb_aux clauses ({literal := negate p, decision := .Deduced} :: trail')
    | _ => false  -- really only [], since backtrack either returns [] or a list with head Guessed
  else
    match unassigned clauses st.trail with
    | [] => true  -- TODO: return a model
    | ls => let l := (List.maximize (posneg_count st.clauses) ls).get!  -- ls is non-empty
            dplb_aux clauses ({literal := l, decision := .Guessed} :: st.trail)
-- termination_by length of {unassigned literals in trail}
decreasing_by sorry

/- DPLL with backjumping and simple clause learning -/
def dplb (clauses: PCNFFormula) : Bool :=
  dplb_aux clauses []

def dplbsat := dplb ∘ CNF.defcnf_opt_sets
def dplbtaut := not ∘ dplbsat ∘ (.Not ·)


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
  /-

  -/
  #guard CNF.print_cnf_formula_sets (CNF.simpcnf not_pqqr)
    ==  [["p", "q"], ["p", "r"], ["q"], ["~p", "~q", "~r"]]

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
