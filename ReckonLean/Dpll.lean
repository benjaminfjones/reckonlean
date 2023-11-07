import ReckonLean.Common
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
    dbg_trace "unit_prop: {print_pf u}"
    let u' := negate u
    let clauses' := List.filter (fun cl => not (List.mem u cl)) clauses
    Set.set_image (fun cl => Set.subtract cl [ u' ]) clauses'

def affirmative_negative_rule (clauses : PCNFFormula) : Option PCNFFormula :=
  let lits := Set.unions clauses
  let (neg', pos) := List.partition negative lits
  let neg := Set.set_image negate neg'
  /- find lits that only appear positively or only appear negatively -/
  let pos_only := Set.subtract pos neg
  dbg_trace "afr: pos_only #{pos_only.length}"
  let neg_only := Set.subtract neg pos
  dbg_trace "arf: neg_only #{neg_only.length}"
  let pure := Set.union pos_only (Set.set_image negate neg_only)
  if pure == [] then none
  else some (List.filter (fun cl => Set.intersect cl pure == []) clauses)

/- Resolve the formula on a literal `p` -/
def resolve_on (lit : Formula Prp) (clauses : PCNFFormula) : PCNFFormula :=
  dbg_trace "resolve_on: {print_pf lit}"
  let lit' := negate lit
  let (pos, notpos) := List.partition (List.mem lit) clauses
  let (neg, other) := List.partition (List.mem lit') notpos
  let pos' := Set.set_image (List.filter (· != lit)) pos
  let neg' := Set.set_image (List.filter (· != lit')) neg
  let res0 := List.all_pairs Set.union pos' neg'
  Set.union other (List.filter (non CNF.trivial) res0)

/- Heuristic for determing how large the formula blow-up is when applying
   `resolve_on` to a given literal. -/
def resolution_blowup (cls : PCNFFormula) (l : Formula Prp) : Int :=
  let m := List.length (List.filter (List.mem l) cls)
  let n := List.length (List.filter (List.mem (negate l)) cls)
  (m * n) - m - n

/- Apply `resolve_on` for the best literal according to heuristics -/
def resolution_rule (clauses: PCNFFormula) : Option PCNFFormula :=
  let pvs := List.filter positive (Set.unions clauses)
  Option.map (fun p => resolve_on p clauses)
    (List.minimize (resolution_blowup clauses) pvs)

/- ------------------------------------------------------------------------- -/
/- Overall procedure.                                                        -/
/- ------------------------------------------------------------------------- -/

def dp (clauses: PCNFFormula) : Bool :=
  if clauses == [] then true
  else if List.mem [] clauses then false
  else
    if let some res := Option.map dp (one_literal_rule clauses) then
      res
    else
      /- `one_literal_rule` doesn't apply any further -/
      if let some res := Option.map dp (affirmative_negative_rule clauses) then
        res
      else
        /- `affirmative_negative_rule` doesn't apply any further -/
        dp (resolution_rule clauses).get!
-- termination_by dp clauses => clauses.length  -- need lemmas about rules
decreasing_by sorry

/- ------------------------------------------------------------------------- -/
/- Davis-Putnam satisfiability tester and tautology checker.                 -/
/- ------------------------------------------------------------------------- -/

def dpsat fm := dp (CNF.defcnf_opt_sets fm)
def dptaut fm := not (dpsat (.Not fm))

namespace Examples

def iff_ex := <<"(p <=> q) <=> ~(r ==> s)">>
/- Prove fm <=> NNF <=> NENF -/
#guard dptaut (.Iff iff_ex (nnf iff_ex))
#guard dptaut (.Iff iff_ex (nenf iff_ex))
/- Prove defcnf_opt fm => fm -/
#guard dptaut (.Imp (CNF.defcnf_opt iff_ex) iff_ex)

end Examples
