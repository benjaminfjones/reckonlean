import Std.Tactic.GuardExpr

import ReckonLean.Common
import ReckonLean.Formulas
import ReckonLean.FPF

/- A type for atomic propositions -/
structure Prp where
  name: String
deriving BEq, Hashable, Ord

def prp := Prp.mk

instance : Repr Prp where
  reprPrec prp _ := prp.name

instance : Inhabited Prp where
  default := ⟨ "p" ⟩

abbrev PFormula := Formula Prp

/- Parsing of propositional formulas -/
def parse_propvar (_vs: ctx) : parser (PFormula) :=
  fun inp =>
    match inp with
    | p :: oinp => if p != "(" then [(Formula.Atom (Prp.mk p), oinp)] else ParseResult.error
    | _ => ParseResult.error

/-
Parse a prop formula

Note the `inp` parser just fails since we don't expect atomic predicates
-/
def parse_prop_formula (inp: String) : Option PFormula :=
  let ifn := fun _ _ => ParseResult.error  /- unsed for prop logic -/
  make_parser (parse_formula (ifn, parse_propvar) []) inp

declare_syntax_cat propf
syntax str : propf  -- strings for parse_prop_formula

/--
Custom notation for translating `propf` into `term`.

The notation won't panic the compiler / IDE if the content doesn't parse. Instead
it returns `Formula.False`.
-/
syntax "<<" propf ">>" : term
macro_rules
| `(<<$s:str>>) => `((parse_prop_formula $s).getD .False)

#guard  <<"p ∧ r">> == Formula.And (Formula.Atom ⟨"p"⟩) (Formula.Atom ⟨"r"⟩)
#guard  <<"p ∧ (q ∨ (r ==> s))">> ==
  Formula.And
    (Formula.Atom ⟨"p"⟩)
    (Formula.Or
      (Formula.Atom ⟨"q"⟩)
      (Formula.Imp
        (Formula.Atom ⟨"r"⟩)
          (Formula.Atom ⟨"s"⟩)))

/- Prop formula Printer -/
def print_prp (_prec: Int) (p: Prp) := p.name
def print_pf := print_qformula print_prp

/-
Examples
-/

/-
Parse errors don't crash the compiler & IDE: warning is emitted and `none` or
`Formula.False` is returned depending on whether the top-level parser is used or
the custom syntax.
-/
#guard parse_prop_formula "p ∧" == none
#guard <<"p ∧">> == .False  -- emits "parse error"

/- round trip -/
#guard print_pf (<<"p ∧ q">>) == "<<p ∧ q>>"
#guard print_pf <<"forall p. p ∨ q">> == "<<forall p. p ∨ q>>"
#guard print_pf << "forall p. (exists q. (p ∨ ~p) ∧ (p ∨ q))">> ==
   "<<forall p. exists q. (p ∨ ~p) ∧ (p ∨ q)>>"  -- true; different parentheses


/- ------------------------------------------------------------------------- -/
/- Simplification and Normal Forms                                           -/
/- ------------------------------------------------------------------------- -/

/- One step prop formula simplification -/
def psimplify1 : Formula α → Formula α
  | .Not .False => .True
  | .Not .True => .False
  | .Not (.Not p) => p
  | .And _p .False | .And .False _p => .False
  | .And p .True | .And .True p => p
  | .Or p .False | .Or .False p => p
  | .Or _p .True | .Or .True _p => .True
  | .Imp .False _p | .Imp _p .True => .True
  | .Imp .True p => p
  | .Imp p .False => .Not p
  | .Iff p .True | .Iff .True p => p
  | .Iff .False .False => .True
  | .Iff p .False | .Iff .False p => .Not p
  | fm => fm

/- Recursive bottom-up prop formula simplification -/
def psimplify : Formula α → Formula α
  | .Not p => psimplify1 (.Not (psimplify p))
  | .And p q => psimplify1 (.And (psimplify p) (psimplify q))
  | .Or p q => psimplify1 (.Or (psimplify p) (psimplify q))
  | .Imp p q => psimplify1 (.Imp (psimplify p) (psimplify q))
  | .Iff p q => psimplify1 (.Iff (psimplify p) (psimplify q))
  | fm => fm

#guard psimplify <<"(true ==> (x <=> false)) ==> ~(y ∨ false ∧ z)">> ==
  .Imp (.Not (.Atom ⟨ "x" ⟩ )) (.Not (.Atom ⟨ "y" ⟩ ))

#guard print_pf (psimplify <<"(true ==> (x <=> false)) ==> ~(y ∨ false ∧ z)">>) ==
  "<<~x ==> ~y>>"


#guard print_pf (psimplify <<"((x ==> y) ==> true) ∨ ~false">>) == "<<true>>"

/- Useful predicates and transformations for literals -/
def negative : Formula α → Bool | .Not _ => true | _ => false
def positive (lit: Formula α) : Bool := not (negative lit)
/- Negate a literal -/
def negate : Formula α → Formula α | .Not p => p | p => .Not p
/- Absolute value of a literal -/
def litabs : (Formula α) → Formula α | .Not p => p | q => q

/- Negation normal form -/
def nnf (fm: Formula α) : Formula α :=
  nnf_aux (psimplify fm)
where
  nnf_aux
    | .And p q => .And (nnf_aux p) (nnf_aux q)
    | .Or p q => .Or (nnf_aux p) (nnf_aux q)
    | .Imp p q => .Or (nnf_aux (.Not p)) (nnf_aux q)
    | .Iff p q =>
        .Or (.And (nnf_aux p) (nnf_aux q)) (.And (nnf_aux (.Not p)) (nnf_aux (.Not q)))
    | .Not (.Not p) => nnf_aux p
    | .Not (.And p q) => .Or (nnf_aux (.Not p)) (nnf_aux (.Not q))
    | .Not (.Or p q) => .And (nnf_aux (.Not p)) (nnf_aux (.Not q))
    | .Not (.Imp p q) => .And (nnf_aux p) (nnf_aux (.Not q))
    | .Not (.Iff p q) =>
        .Or (.And (nnf_aux p) (nnf_aux (.Not q))) (.And (nnf_aux (.Not p)) (nnf_aux q))
    | f => f
decreasing_by sorry  /- use (depth)-(min depth of .Not) ? -/

/- Simple negation-pushing; does not eliminate Iff -/
def nenf : Formula α → Formula α :=
  nenf_aux ∘ psimplify
where
  nenf_aux : Formula α → Formula α
    | .Not (.Not p) => nenf_aux p
    | .Not (.And p q) => .Or (nenf_aux (.Not p)) (nenf_aux (.Not q))
    | .Not (.Or p q) => .And (nenf_aux (.Not p)) (nenf_aux (.Not q))
    | .Not (.Imp p q) => .And (nenf_aux p) (nenf_aux (.Not q))
    | .Not (.Iff p q) => .Iff (nenf_aux p) (nenf_aux (.Not q))
    | .And p q => .And (nenf_aux p) (nenf_aux q)
    | .Or p q => .Or (nenf_aux p) (nenf_aux q)
    | .Imp p q => .Or (nenf_aux (.Not p)) (nenf_aux q)
    | .Iff p q => .Iff (nenf_aux p) (nenf_aux q)
    | fm => fm
decreasing_by sorry

/-
Not gonna guard this one :sweat:

Or (And (Or (And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r
s)))) (And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s)))))
(And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s))))) (And (Or
(And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s)))) (And (Iff
(Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s))))) (Or (Iff (Iff p q)
(Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s)))))
-/
#eval nnf <<"(p <=> q) <=> ~(r ==> s)">>
#guard nenf <<"(p <=> q) <=> ~(r ==> s)">> ==
  .Iff
    (.Iff (.Atom ⟨ "p" ⟩ ) (.Atom ⟨ "q" ⟩ ))
    (.And (.Atom ⟨"r"⟩ ) (.Not (.Atom ⟨ "s" ⟩ )))
/- TODO: prove these are both equivalent to the original formula -/

def list_conj {α : Type} [Inhabited α] : List (Formula α) → Formula α
  | [] => .True | l => List.end_itlist mk_and l
def list_disj {α : Type} [Inhabited α] : List (Formula α) → Formula α
  | [] => .False | l => List.end_itlist mk_or l

namespace DNF
/- ------------------------------------------------------------------------- -/
/- Disjunctive Normal Form (DNF)                                             -/
/-                                                                           -/
/- Note: most of this isn't ported from the reckoning development, only some -/
/- minor definitions.                                                        -/
/- ------------------------------------------------------------------------- -/

variable {α : Type} [Inhabited α] [Ord α] [BEq α]

abbrev DNFFormula (α: Type) := List (List (Formula α))
def print_dnf_formula_sets := List.map (List.map (print_qliteral print_prp))

/--
Determine if the conjunction of literals is contradictory, i.e.
contains both p and ~p for some atomic prop p.

Note: this is the same exact function as `CNF.trivial` below, as a function
on sets of sets. It's repeated here to clarify the different meaning when we're
operating on conjunctions of literals vs. disjunctions of literals.
-/
def contra (lits: List (Formula α)) : Bool :=
  let (pos, neg) := List.partition positive lits
  Set.intersect pos (List.map negate neg) != []

/-- Distribute for the set of sets representation -/
def pure_distrib (s1 s2: DNFFormula α) := Set.setify (List.all_pairs Set.union s1 s2)

/-- Convert to DNF, by transformation, in set of sets form -/
def purednf (fm: Formula α) :=
  match fm with
  | .And p q => pure_distrib (purednf p) (purednf q)
  | .Or p q => Set.union (purednf p) (purednf q)
  | _ => [ [ fm ] ]

/-- Convert to DNF and simplify -/
def simpdnf (fm: Formula α) :=
  match fm with
  | .False => []
  | .True => [ [] ]
  | _ =>
      /- Filter out trivial disjuncts -/
      let djs := List.filter (non contra) (purednf (nnf fm))
      /- Filter out subsumed disjuncts -/
      List.filterTR (fun d => not (List.any djs (fun d' => Set.psubset d' d))) djs

-- This example is close to CNF, but not quite
def distrib_ex1 := <<"(p ∨ q ∧ r) ∧ (~p ∨ ~r)">>

-- In this example, which is in CNF, distrib produces DNF
def distrib_ex2 := <<"(p ∨ q ∨ r) ∧ (~p ∨ ~r)">>

-- trivial ∘ purednf
#guard print_dnf_formula_sets (List.filter (non contra) (purednf distrib_ex1)) ==
  [["p", "~r"], ["q", "r", "~p"]]

-- simpdnf distrib_ex1
#guard print_dnf_formula_sets (simpdnf distrib_ex1) == [["p", "~r"], ["q", "r", "~p"]]

-- simpdnf distrib_ex2
#eval print_dnf_formula_sets (simpdnf distrib_ex2) == [["p", "~r"], ["q", "~p"], ["q", "~r"], ["r", "~p"]]

end DNF

namespace CNF
/- ------------------------------------------------------------------------- -/
/- Conjuctive Normal Form (CNF)                                              -/
/- ------------------------------------------------------------------------- -/

/- Compute a CNF representation, in set of sets form.contents

   Note: the structure is almost exactly the same as `purednf` modulo swapping
   And/Or by duality.

   For example:

   purecnf (p ∧ q) => union [[p]] [[q]]
                     => [[p]; [q]]

   purecnf (p ∨ q) => pure_distrib [[p]] [[q]]
                     => setify (allpairs union [[p]] [[q]])
                     => setify ([[p; q]])
                     => [[p; q]]
-/
variable {α : Type} [Inhabited α] [Ord α] [BEq α]
abbrev CNFFormula (α: Type) := List (List (Formula α))

abbrev PCNFFormula := CNFFormula Prp

def print_cnf_formula_sets := List.map (List.map (print_qliteral print_prp))

/- Distribute for the set of sets representation -/
def pure_distrib (s1 s2: CNFFormula α) : CNFFormula α :=
  Set.setify (List.all_pairs Set.union s1 s2)

/-
Determine if the disjunction of literals is trivial (a tautology), i.e.
contains both p and ~p for some atomic prop p.
-/
def trivial (lits: List (Formula α)) : Bool :=
  let (pos, neg) := List.partition positive lits
  Set.intersect pos (List.map negate neg) != []

def purecnf : Formula α → CNFFormula α
  | .And p q => Set.union (purecnf p) (purecnf q)
  | .Or p q => pure_distrib (purecnf p) (purecnf q)
  | fm => [ [ fm ] ]

def simpcnf : Formula α → CNFFormula α
  | .False => [ [] ]
  | .True => []
  | fm =>
      /- Filter out trivial conjuncts (i.e. ones that are tautologies) -/
      let cjs := List.filter (fun dj => !(trivial dj) ) (purecnf (nnf fm))
      /- Filter out subsumed conjuncts -/
      let subsumed (c c': List (Formula α)) : Bool := Set.psubset c' c
      let redundant c := Option.isNone (List.find? (subsumed c) cjs)
      List.filter redundant cjs

/- The ultimate evolution of CNF -/
def cnf (fm: Formula α) : Formula α := list_conj (List.map list_disj (simpcnf fm))


/- ------------------------------------------------------------------------- -/
/- Definitional Conjuctive Normal Form (Tseitin Transformation)              -/
/- ------------------------------------------------------------------------- -/

def freshprop (n: Nat) : PFormula × Nat := (.Atom ⟨s!"p_{n}" ⟩, n + 1)

open FPF
structure CNFState where
  formula : PFormula
  defs : Func PFormula (PFormula × PFormula)
  index : Nat

/-
`defcnf_inner` and `defstep` are mutually recursive functions used in the
state transformer loop that produces definitional CNF. The state being
transformed is the triple (formula, definitions so far, fresh prop index)
-/

/-!
Match the top-level connective and use `defstep` to perform the
transform.

`defstep` performs a definition Tseitin step.

The transformation is applied to the args sequentially and then
to the parent formula. If the parent has already been substituted for in
a previous step, it's substitution is reused.
-/
def defcnf_inner (st: CNFState) : CNFState :=
  -- assumption: `fm` is in NENF form
  match st.formula with
  | .And p q => defstep mk_and p q st
  | .Or p q => defstep mk_or p q st
  | .Iff p q => defstep mk_iff p q st
  | _ => st
where
  defstep (op : PFormula → PFormula → PFormula) (arg1 arg2: PFormula) (st: CNFState) : CNFState :=
    let st1 := defcnf_inner {st with formula := arg1}
    let st2 := defcnf_inner {st1 with formula := arg2}
    let fm' := op st1.formula st2.formula
    let mlookup := apply? st2.defs fm'
    match mlookup with
    | some v => {st2 with formula := v.fst}
    | none =>
      let (v, n3) := freshprop st2.index
      {formula := v, defs := (v |-> (fm', Formula.Iff v fm')) st2.defs, index := n3}
  decreasing_by sorry

/-
Helper function for finding the next unsed prop variable index.

It returns the max of `n` and the smallest non-negative integer `k` such
that `str` is `prefix ^ suffix`, `suffix` represents an int, and
`int_of_string suffix <= k`. `n` is the default
-/
def max_varindex (pfx str: String) (n: Nat): Nat :=
  let m := pfx.length
  let l := str.length
  if l <= m || String.copySlice str 0 m != pfx then n
  else
    let s' := String.copySlice str m l
    if List.all s'.toList numeric then Nat.max n (String.toNat! s')
    else n

#guard max_varindex "p" "p5" 4 == 5
#guard max_varindex "p" "p5" 6 == 6
#guard max_varindex "q" "p5" 8 == 8
#guard max_varindex "q" "foobar" 0 == 0

def mk_defcnf (fn: CNFState → CNFState) (fm: PFormula) : PCNFFormula :=
  let fm' := nenf fm
  let n := 1 + overatoms (fun p n => max_varindex "p_" p.name n) fm' 0
  let st := fn {formula := fm', defs := undefined, index := n}
  let deflist := List.map (fun tt => tt.snd.snd ) (graph st.defs)
  Set.unions (simpcnf st.formula :: List.map simpcnf deflist)

def defcnf_sets (fm: PFormula) : PCNFFormula := mk_defcnf defcnf_inner fm
def defcnf (fm: PFormula) : PFormula := list_conj (List.map list_disj (defcnf_sets fm))

/-!
Optimized version of defcnf

 1. preserve outter conjunctive structure: only defcnf the conjuncts
 2. in a conjunct, leave atomic parts of disjunts alone (do not make new definitions for them)

-/

/-!
The state transformer part of `defcnf_inner` above, but without intro'ing new
definitions.
-/
def subcnf (sfn: CNFState → CNFState) (op: PFormula → PFormula → PFormula)
           (p q: PFormula) (st: CNFState) : CNFState :=
  let st1 := sfn { st with formula := p }
  let st2 := sfn { st1 with formula := q }
  { formula := op st1.formula st2.formula, defs := st2.defs, index := st2.index }

def orcnf (st: CNFState) : CNFState :=
  match st.formula with
  | .Or p q => subcnf orcnf mk_or p q st
  | _ => defcnf_inner st
decreasing_by sorry

def andcnf (st: CNFState) : CNFState :=
  match st.formula with
  | .And p q => subcnf andcnf mk_and p q st
  | _ => orcnf st
decreasing_by sorry

/- Optimized defcnf on the set of sets representation -/
def defcnf_opt_sets : PFormula → PCNFFormula := mk_defcnf andcnf

/- Optimized defcnf on the PFormula representatin -/
def defcnf_opt : PFormula → PFormula := list_conj ∘ (List.map list_disj) ∘ defcnf_opt_sets

end CNF

namespace Examples

open CNF

#guard print_pf (psimplify <<"(false ∧ p ∧ q) ∧ ~(r ∧ s)">>) == "<<false>>"
#guard print_pf (psimplify <<"(p ∧ q) ∧ ~(r ∧ s)">>) == "<<(p ∧ q) ∧ ~(r ∧ s)>>"
#guard print_pf (nnf <<"(p ∧ ~q) ∧ ~(r ∧ s)">>) == "<<(p ∧ ~q) ∧ (~r ∨ ~s)>>"
#guard simpcnf <<"(p ∧ q) ∧ ~(r ∧ s)">> == [[<<"p">>], [<<"q">>], [<<"~r">>, <<"~s">>]]
#guard print_pf (cnf <<"(p ∧ q) ∧ ~(r ∧ s)">>) == "<<p ∧ q ∧ (~r ∨ ~s)>>"


/- Trivial example: all the gory details in `mkdefcnf`, `andcnf`, ...  -/
def triv := <<"p ∧ q">>
#guard print_pf (nenf triv) == "<<p ∧ q>>"
#guard 1 + overatoms (fun p n => max_varindex "p_" p.name n) triv 0 == 1
def triv_final_st := (andcnf {formula := triv, defs := FPF.undefined, index := 1})
#guard triv_final_st.formula == Formula.And <<"p">> <<"q">>
#guard FPF.to_list triv_final_st.defs == []
#guard simpcnf <<"p ∧ q">> == [[<<"p">>], [<<"q">>]]
#guard Set.unions [simpcnf <<"p ∧ q">>] == [[<<"p">>], [<<"q">>]]
#guard print_cnf_formula_sets (defcnf_opt_sets triv) == [["p"], ["q"]]
#guard print_cnf_formula_sets (defcnf_opt_sets triv) == [["p"], ["q"]]

/- Tseitin transformation of Iff results in 11 logical connectives: -/
#guard print_pf (cnf <<"(p <=> (q <=> r))">>) ==
  "<<(p ∨ q ∨ r) ∧ (p ∨ ~q ∨ ~r) ∧ (q ∨ ~p ∨ ~r) ∧ (r ∨ ~p ∨ ~q)>>"

#guard simpcnf <<"(p <=> q) <=> ~(r ==> s)">> ==
  [[<<"p">>, <<"q">>, <<"r">>],
   [<<"p">>, <<"q">>, .Not <<"s">>],
   [<<"p">>, <<"s">>, .Not <<"q">>, .Not <<"r">>],
   [<<"q">>, <<"s">>, .Not <<"p">>, .Not <<"r">>],
   [<<"r">>, .Not <<"p">>, .Not <<"q">>],
   [.Not <<"p">>, .Not <<"q">>, .Not <<"s">>]]


/- --------------------------------------------------------------- -/
/- Example 1: running example in the Handbook                      -/
/- --------------------------------------------------------------- -/
def ex1 := <<"(p ∨ q ∧ r) ∧ (~p ∨ ~r)">>

#guard print_pf (cnf ex1) == "<<(p ∨ q) ∧ (p ∨ r) ∧ (~p ∨ ~r)>>"
#guard print_pf (defcnf ex1) ==
  ("<<(p ∨ p_1 ∨ ~p_2) ∧ (p ∨ p_3) ∧ (p_1 ∨ ~q ∨ ~r) ∧ (p_2 ∨ ~p) ∧ (p_2 ∨ ~p_1) ∧ " ++
  "(p_2 ∨ ~p_4) ∧ (p_3 ∨ r) ∧ (p_3 ∨ ~p_4) ∧ p_4 ∧ (p_4 ∨ ~p_2 ∨ ~p_3) ∧ (q ∨ ~p_1) ∧ " ++
  "(r ∨ ~p_1) ∧ (~p ∨ ~p_3 ∨ ~r)>>")

/- 13 clauses -/
#guard print_cnf_formula_sets (defcnf_sets ex1) ==
  [["p", "p_1", "~p_2"],
   ["p", "p_3"],
   ["p_1", "~q", "~r"],
   ["p_2", "~p"],
   ["p_2", "~p_1"],
   ["p_2", "~p_4"],
   ["p_3", "r"],
   ["p_3", "~p_4"],
   ["p_4"],
   ["p_4", "~p_2", "~p_3"],
   ["q", "~p_1"],
   ["r", "~p_1"],
   ["~p", "~p_3", "~r"]]

/- Optimized version has 5 clauses -/
#guard print_cnf_formula_sets (defcnf_opt_sets ex1)
  == [["p", "p_1"], ["p_1", "~q", "~r"], ["q", "~p_1"], ["r", "~p_1"], ["~p", "~r"]]

/- --------------------------------------------------------------- -/
/- Example 2: already in CNF, blows up to 13 clauses in defcnf     -/
/- --------------------------------------------------------------- -/
def ex2 := <<"(p ∨ q ∨ r) ∧ (~p ∨ ~r)">>

/- plain cnf -/
#guard print_pf (cnf ex2) == "<<(p ∨ q ∨ r) ∧ (~p ∨ ~r)>>"

/- defcnf -/
#guard print_pf (defcnf ex2) ==
  ("<<(p ∨ p_1 ∨ ~p_2) ∧ (p ∨ p_3) ∧ (p_1 ∨ ~q) ∧ (p_1 ∨ ~r) ∧ (p_2 ∨ ~p) ∧ " ++
  "(p_2 ∨ ~p_1) ∧ (p_2 ∨ ~p_4) ∧ (p_3 ∨ r) ∧ (p_3 ∨ ~p_4) ∧ p_4 ∧ (p_4 ∨ ~p_2 ∨ ~p_3) ∧ " ++
  "(q ∨ r ∨ ~p_1) ∧ (~p ∨ ~p_3 ∨ ~r)>>")

/- defcnf_sets -/
#guard print_cnf_formula_sets (defcnf_sets ex2) ==
  [["p", "p_1", "~p_2"],
   ["p", "p_3"],
   ["p_1", "~q"],
   ["p_1", "~r"],
   ["p_2", "~p"],
   ["p_2", "~p_1"],
   ["p_2", "~p_4"],
   ["p_3", "r"],
   ["p_3", "~p_4"],
   ["p_4"],
   ["p_4", "~p_2", "~p_3"],
   ["q", "r", "~p_1"],
   ["~p", "~p_3", "~r"]]

/- Optimized version intros no additional prop variables -/
#eval print_cnf_formula_sets (defcnf_opt_sets ex2)
  == [["p", "q", "r"], ["~p", "~r"]]

/- --------------------------------------------------------------- -/
/- Example 3: 3-clause basic cnf, blows up to 10 clauses in defcnf -/
/- --------------------------------------------------------------- -/
def ex3 := <<"(p ∨ (q ∧ ~r)) ∧ s">>

/- plain cnf -/
#guard print_pf (cnf ex3) == "<<(p ∨ q) ∧ (p ∨ ~r) ∧ s>>"

/- defcnf -/
#guard print_pf (defcnf ex3) ==
  "<<(p ∨ p_1 ∨ ~p_2) ∧ (p_1 ∨ r ∨ ~q) ∧ (p_2 ∨ ~p) ∧ (p_2 ∨ ~p_1) ∧ (p_2 ∨ ~p_3) ∧ " ++
  "p_3 ∧ (p_3 ∨ ~p_2 ∨ ~s) ∧ (q ∨ ~p_1) ∧ (s ∨ ~p_3) ∧ (~p_1 ∨ ~r)>>"

/- defcnf_sets: 10 clauses -/
#guard print_cnf_formula_sets (defcnf_sets ex3) ==
  [["p", "p_1", "~p_2"],
   ["p_1", "r", "~q"],
   ["p_2", "~p"],
   ["p_2", "~p_1"],
   ["p_2", "~p_3"],
   ["p_3"],
   ["p_3", "~p_2", "~s"],
   ["q", "~p_1"],
   ["s", "~p_3"],
   ["~p_1", "~r"]]

/- optimized: 5 clauses -/
#guard print_cnf_formula_sets (defcnf_opt_sets ex3)
  == [["p", "p_1"], ["p_1", "r", "~q"], ["q", "~p_1"], ["s"], ["~p_1", "~r"]]

/- --------------------------------------------------------------- -/
/- Example 4: Nested Equivalence                                   -/
/- --------------------------------------------------------------- -/

#guard print_pf (nnf <<"(p <=> q) <=> ~(r ==> s)">>) ==
  "<<(p ∧ q ∨ ~p ∧ ~q) ∧ r ∧ ~s ∨ (p ∧ ~q ∨ ~p ∧ q) ∧ (~r ∨ s)>>"

#guard print_pf (cnf <<"(p <=> q) <=> ~(r ==> s)">>) ==
  "<<(p ∨ q ∨ r) ∧ (p ∨ q ∨ ~s) ∧ (p ∨ s ∨ ~q ∨ ~r) ∧ (q ∨ s ∨ ~p ∨ ~r) ∧ (r ∨ ~p ∨ ~q) ∧ (~p ∨ ~q ∨ ~s)>>"

#guard print_pf (defcnf <<"(p <=> q) <=> ~(r ==> s)">>) ==
  "<<(p ∨ p_1 ∨ q) ∧ (p ∨ ~p_1 ∨ ~q) ∧ (p_1 ∨ p_2 ∨ p_3) ∧ (p_1 ∨ ~p ∨ ~q) ∧ " ++
  "(p_1 ∨ ~p_2 ∨ ~p_3) ∧ (p_2 ∨ s ∨ ~r) ∧ (p_2 ∨ ~p_1 ∨ ~p_3) ∧ p_3 ∧ " ++
  "(p_3 ∨ ~p_1 ∨ ~p_2) ∧ (q ∨ ~p ∨ ~p_1) ∧ (r ∨ ~p_2) ∧ (~p_2 ∨ ~s)>>"

#eval print_pf (defcnf_opt <<"(p <=> q) <=> ~(r ==> s)">>)
  == "<<(p ∨ p_1 ∨ q) ∧ (p ∨ ~p_1 ∨ ~q) ∧ (p_1 ∨ p_2 ∨ p_3) ∧ (p_1 ∨ ~p ∨ ~q) ∧ " ++
  "(p_1 ∨ ~p_2 ∨ ~p_3) ∧ (p_2 ∨ s ∨ ~r) ∧ (p_2 ∨ ~p_1 ∨ ~p_3) ∧ p_3 ∧ " ++
  "(p_3 ∨ ~p_1 ∨ ~p_2) ∧ (q ∨ ~p ∨ ~p_1) ∧ (r ∨ ~p_2) ∧ (~p_2 ∨ ~s)>>"

end Examples
