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
  dbg_trace "anr: pos_only #{pos_only.length}"
  let neg_only := Set.subtract neg pos
  dbg_trace "anr: neg_only #{neg_only.length}"
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


/- ========================================================================= -/
/- EXAMPLES                                                                  -/
/- ========================================================================= -/

namespace Examples

/- Alises just for this section -/
def satisfiable := dpsat
def tautology := dptaut

/- Simple equivalence proof for `nnf` and `nenf` from Prop -/
def iff_ex := <<"(p <=> q) <=> ~(r ==> s)">>
/- Prove fm <=> NNF <=> NENF -/
#guard dptaut (.Iff iff_ex (nnf iff_ex))
#guard dptaut (.Iff iff_ex (nenf iff_ex))
/- Prove defcnf_opt fm => fm -/
#guard dptaut (.Imp (CNF.defcnf_opt iff_ex) iff_ex)

/- ------------------- -/
/- Lots of tautologies -/
/- ------------------- -/

/- "tautology: and_comm" -/
#guard tautology <<"p ∧ q <=> q ∧ p">>

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
  #guard tautology (Formula.Iff (nenf not_pqqr) (nnf not_pqqr))
  #guard tautology (Formula.Iff (not_pqqr) (nnf not_pqqr))
  #guard not (tautology (Formula.Iff (pqqr) (nnf not_pqqr)))
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

end Examples
