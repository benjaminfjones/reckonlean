import ReckonLean.Common
import ReckonLean.Formulas
import ReckonLean.Prop
import ReckonLean.Dpll

/- ------------------------------------------------------------------------- -/
/- Tests of an encoding of a Ramsey-like Theorem                             -/
/- ------------------------------------------------------------------------- -/

/- Encodes a prop formula expressing the property that
   in an arbitrary graph of size `n` there is either a fully
   connected subgraph of size `s`, or a fully disconnected
   subgraph of size `t`.

   If `ramsey s t n` is a tautology, then R(s,t), the size of the minimal such
   graph, is  <:= n.

   Note: R(s, t) <:= R(s, t-1) + R(s-1, t)
-/
def ramsey (s t n: Nat) : PFormula :=
  let verts := List.drop 1 $ List.range (n+1)
  let conn_grps := Set.allsubsets s verts
  let dis_grps := Set.allsubsets t verts
  let pairs_of_grp : List Nat → List (Nat × Nat) := List.distinct_pairs
  let atom_of_pair (p: Nat × Nat) : PFormula :=
    Formula.Atom ⟨ s!"p{p.fst}{p.snd}" ⟩

  let comp_connected (grp: List Nat) : PFormula :=
    List.foldr mk_and Formula.True (List.map atom_of_pair (pairs_of_grp grp))

  let comp_disconnected (grp: List Nat) : PFormula :=
    List.foldr mk_and
      Formula.True
      (List.map (fun p => Formula.Not (atom_of_pair p)) (pairs_of_grp grp))

  Formula.Or
    (List.foldr mk_or Formula.False (List.map comp_connected conn_grps))
    (List.foldr mk_or Formula.False  (List.map comp_disconnected dis_grps))

open List

def ex_3_3_6 := ramsey 3 3 6
#eval length (atoms ex_3_3_6)  -- 15 variables
#eval length (CNF.defcnf_opt_sets ex_3_3_6)  -- 241 clauses
#eval length (CNF.defcnf_opt_sets (.Not ex_3_3_6))  -- 40 clauses in tautology form
#eval maximize id $ map length (CNF.defcnf_opt_sets (.Not ex_3_3_6))  -- largest clause has 3 literals

def ex_3_4_9 := ramsey 3 4 9
#eval length (atoms ex_3_4_9)  -- 36 variables
#eval length (CNF.defcnf_opt_sets ex_3_4_9)  -- 2395 clauses
#eval length (CNF.defcnf_opt_sets (.Not ex_3_4_9))  -- 210 clauses in tautology form
#eval maximize id $ map length (CNF.defcnf_opt_sets (.Not ex_3_4_9))  -- largest clause has 6 literals
