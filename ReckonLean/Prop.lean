import ReckonLean.Common
import ReckonLean.Formulas
import ReckonLean.FPF

/- A type for atomic propositions -/
structure Prp where
  name: String
deriving BEq, Hashable, Ord

instance : Repr Prp where
  reprPrec prp _ := prp.name

instance : Inhabited Prp where
  default := ⟨ "p" ⟩

abbrev PFormula := Formula Prp

/- Parsing of propositional formulas -/
def parse_propvar (_vs: ctx) : parser (Option (PFormula)) :=
  fun inp =>
    match inp with
    | p :: oinp => if p != "(" then (some (Formula.Atom ⟨ p ⟩), oinp) else (none, inp)
    | _ => (none, inp)

/-
Parse a prop formula

Note the `inp` parser just fails since we don't expect atomic predicates
-/
def parse_prop_formula (inp: String) : PFormula :=
  let ifn := fun (_ctx: ctx) (toks: tokens) => (none, toks)  /- unsed for prop logic -/
  make_parser (parse_formula (ifn, parse_propvar) []) inp

declare_syntax_cat propf
syntax str : propf  -- strings for parse_prop_formula

-- auxiliary notation for translating `propf` into `term`
syntax "<<" propf ">>" : term
macro_rules
| `(<<$s:str>>) => `(parse_prop_formula $s)

#check <<"p ∧ q">>
#eval  <<"p ∧ r">>
#eval  <<"p ∧ (q ∨ (r ==> s))">>

/- Prop formula Printer -/
def print_propvar (_prec: Int) (p: Prp) := p.name
def print_prop_formula := print_qformula print_propvar

/-
Examples
-/

/- round trip -/
#eval print_prop_formula (<<"p ∧ q">>) == "<<p ∧ q>>"  -- true
/- `rfl` won't close this for some reason, the LHS fails to evaluate fully
set_option trace.profiler true
example : print_prop_formula <<"p /\\ q">> = "<<p /\\ q>>" := by rfl
-/

#eval print_prop_formula <<"forall p. p ∨ q">> == "<<forall p. p ∨ q>>"  -- true
#eval print_prop_formula << "forall p. (exists q. (p ∨ ~p) ∧ (p ∨ q))">> ==
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

/- Imp (Not x) (Not y) -/
#eval psimplify <<"(true ==> (x <=> false)) ==> ~(y ∨ false ∧ z)">>
/- <<~x ==> ~y>> -/
#eval print_prop_formula (psimplify <<"(true ==> (x <=> false)) ==> ~(y ∨ false ∧ z)">>)

/- <<true>> -/
#eval print_prop_formula (psimplify <<"((x ==> y) ==> true) ∨ ~false">>)

/- Useful predicates and transformations for literals -/
def negative : Formula α → Bool | .Not _ => true | _ => false
def positive (lit: Formula α) : Bool := not (negative lit)
def negate : Formula α → Formula α | .Not p => p | p => .Not p

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
Or (And (Or (And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r
s)))) (And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s)))))
(And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s))))) (And (Or
(And (Iff (Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s)))) (And (Iff
(Iff p q) (Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s))))) (Or (Iff (Iff p q)
(Not (Imp r s))) (Iff (Iff p q) (Not (Imp r s)))))
-/
#eval nnf <<"(p <=> q) <=> ~(r ==> s)">>
/-
Iff (Iff p q) (And r (Not s))
-/
#eval nenf <<"(p <=> q) <=> ~(r ==> s)">>
/- TODO: prove these are both equivalent to the original formula -/

def list_conj {α : Type} [Inhabited α] : List (Formula α) → Formula α
  | [] => .True | l => List.end_itlist mk_and l
def list_disj {α : Type} [Inhabited α] : List (Formula α) → Formula α
  | [] => .False | l => List.end_itlist mk_or l

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

def print_cnf_formula_sets := List.map (List.map (print_qliteral print_propvar))

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

#eval max_varindex "p" "p5" 4  -- 5
#eval max_varindex "p" "p5" 6  -- 6
#eval max_varindex "q" "p5" 8  -- 8
#eval max_varindex "q" "foobar" 0  -- 0

def mk_defcnf (fn: CNFState → CNFState) (fm: PFormula) : PCNFFormula :=
  let fm' := nenf fm
  let n := 1 + overatoms (fun p n => max_varindex "p_" p.name n) fm' 0
  let st' := fn {formula := fm', defs := undefined, index := n}
  let deflist := List.map (fun tt => tt.snd.snd ) (graph st'.defs)
  Set.unions (simpcnf st'.formula :: List.map simpcnf deflist)

def defcnf_sets (fm: PFormula) : PCNFFormula := mk_defcnf defcnf_inner fm
def defcnf (fm: PFormula) : PFormula := list_conj (List.map list_disj (defcnf_sets fm))

end CNF

namespace Examples

open CNF

#eval psimplify <<"(p ∧ q) ∧ ~(r ∧ s)">>
#eval nnf <<"(p ∧ q) ∧ ~(r ∧ s)">>
#eval simpcnf <<"(p ∧ q) ∧ ~(r ∧ s)">> == [[<<"p">>], [<<"q">>], [<<"~r">>, <<"~s">>]]
/-
"<<p ∧ q ∧ (~r ∨ ~s)>>"
-/
#eval print_prop_formula (cnf <<"(p ∧ q) ∧ ~(r ∧ s)">>)

/-
Tseitin transformation of Iff results in 11 logical connectives:

"<<(p ∨ q ∨ r) ∧ (p ∨ ~q ∨ ~r) ∧ (q ∨ ~p ∨ ~r) ∧ (r ∨ ~p ∨ ~q)>>"
-/
#eval print_prop_formula (cnf <<"(p <=> (q <=> r))">>)

/-
[[p, q, r], [p, q, Not s], [p, s, Not q, Not r], [q, s, Not p, Not r], [r, Not
p, Not q], [Not p, Not q, Not s]]
-/
#eval simpcnf <<"(p <=> q) <=> ~(r ==> s)">>

/- --------------------------------------------------------------- -/
/- Example 1: running example in the Handbook                      -/
/- --------------------------------------------------------------- -/
def ex1 := <<"(p ∨ q ∧ r) ∧ (~p ∨ ~r)">>
/-
"<<(p ∨ q) ∧ (p ∨ r) ∧ (~p ∨ ~r)>>"
-/
#eval print_prop_formula (cnf ex1)
/-
"<<(p ∨ p_1 ∨ ~p_2) ∧ (p ∨ p_3) ∧ (p_1 ∨ ~q ∨ ~r) ∧ (p_2 ∨ ~p) ∧ (p_2 ∨ ~p_1) ∧ (p_2 ∨ ~p_4) ∧ (p_3 ∨ r) ∧ (p_3 ∨ ~p_4) ∧ p_4 ∧ (p_4 ∨ ~p_2 ∨ ~p_3) ∧ (q ∨ ~p_1) ∧ (r ∨ ~p_1) ∧ (~p ∨ ~p_3 ∨ ~r)>>"
-/
#eval print_prop_formula (defcnf ex1)
/-
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

-/
#eval print_cnf_formula_sets (defcnf_sets ex1)

/- --------------------------------------------------------------- -/
/- Example 2: already in CNF, blows up to 13 clauses in defcnf     -/
/- --------------------------------------------------------------- -/
def ex2 := <<"(p ∨ q ∨ r) ∧ (~p ∨ ~r)">>

/-
"<<(p ∨ q ∨ r) ∧ (~p ∨ ~r)>>"
-/
#eval print_prop_formula (cnf ex2)

/-
"<<(p ∨ p_1 ∨ ~p_2) ∧ (p ∨ p_3) ∧ (p_1 ∨ ~q) ∧ (p_1 ∨ ~r) ∧ (p_2 ∨ ~p) ∧ (p_2 ∨ ~p_1) ∧ (p_2 ∨ ~p_4) ∧ (p_3 ∨ r) ∧ (p_3 ∨ ~p_4) ∧ p_4 ∧ (p_4 ∨ ~p_2 ∨ ~p_3) ∧ (q ∨ r ∨ ~p_1) ∧ (~p ∨ ~p_3 ∨ ~r)>>"
-/
#eval print_prop_formula (defcnf ex2)

/-
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
-/
#eval print_cnf_formula_sets (defcnf_sets ex2)

/- --------------------------------------------------------------- -/
/- Example 3: 3-clause basic cnf, blows up to 10 clauses in defcnf -/
/- --------------------------------------------------------------- -/
def ex3 := <<"(p ∨ (q ∧ ~r)) ∧ s">>

/-
"<<(p ∨ q) ∧ (p ∨ ~r) ∧ s>>"
-/
#eval print_prop_formula (cnf ex3)

/-
"<<(p ∨ p_1 ∨ ~p_2) ∧ (p_1 ∨ r ∨ ~q) ∧ (p_2 ∨ ~p) ∧ (p_2 ∨ ~p_1) ∧ (p_2 ∨ ~p_3) ∧ p_3 ∧ (p_3 ∨ ~p_2 ∨ ~s) ∧ (q ∨ ~p_1) ∧ (s ∨ ~p_3) ∧ (~p_1 ∨ ~r)>>"
-/
#eval print_prop_formula (defcnf ex3)

/-
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
-/
#eval print_cnf_formula_sets (defcnf_sets ex3)

end Examples
