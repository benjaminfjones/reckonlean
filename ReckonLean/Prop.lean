import ReckonLean.Common
import ReckonLean.Formulas

/- A type for atomic propositions -/
structure Prp where
  name: String
deriving BEq, Ord

instance : Repr Prp where
  reprPrec prp _ := prp.name

instance : Inhabited Prp where
  default := ⟨ "p" ⟩

/- Parsing of propositional formulas -/
def parse_propvar (_vs: ctx) : parser (Option (Formula Prp)) :=
  fun inp =>
    match inp with
    | p :: oinp => if p != "(" then (some (Formula.Atom ⟨ p ⟩), oinp) else (none, inp)
    | _ => (none, inp)

/-
Parse a prop formula

Note the `inp` parser just fails since we don't expect atomic predicates
-/
def parse_prop_formula (inp: String) : Formula Prp :=
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

#eval psimplify <<"(p ∧ q) ∧ ~(r ∧ s)">>
#eval nnf <<"(p ∧ q) ∧ ~(r ∧ s)">>
#eval simpcnf <<"(p ∧ q) ∧ ~(r ∧ s)">> == [[<<"p">>], [<<"q">>], [<<"~r">>, <<"~s">>]]
/-
"<<p ∧ q ∧ (~r ∨ ~s)>>"
-/
#eval print_prop_formula (cnf <<"(p ∧ q) ∧ ~(r ∧ s)">>)

/-
[[p, q, r], [p, q, Not s], [p, s, Not q, Not r], [q, s, Not p, Not r], [r, Not
p, Not q], [Not p, Not q, Not s]]
-/
#eval simpcnf <<"(p <=> q) <=> ~(r ==> s)">>


/- ------------------------------------------------------------------------- -/
/- Definitional Conjuctive Normal Form (Tseitin Transformation)              -/
/- ------------------------------------------------------------------------- -/

def freshprop (n: Int) : Formula Prp × Int := (.Atom ⟨s!"p_{n}" ⟩, n + 1)

abbrev Defs := Unit  -- TODO: Func Prp (Formula Prp)
structure CNFState where
  formula : Formula Prp
  defs : Defs
  index : Int

/-
/-
`defcnf_inner` and `defstep` are mutually recursive functions used in the
state transformer loop that produces definitional CNF. The state being
transformed is the triple (formula, definitions so far, fresh prop index)
-/
mutual
def defcnf_inner (st: CNFState) :=
  -- assumption: `fm` is in NENF form
  match st.formula with
  | .And p q => defstep mk_and p q trip
  | .Or p q => defstep mk_or p q trip
  | .Iff p q => defstep mk_iff p q trip
  | _ => trip

/- perform a definition Tseitin step -/
def defstep op args st :=
  let (p, q) := args
  let st1 := defcnf_inner st
  let st2 := defcnf_inner (q, defs1, n1)
  let fm' := op fm1 fm2
  let mlookup := (apply defs2 fm')
  match mlookup with
  | some v => CNFState {formula: fst v, defs: defs2, index: n2}
  | none =>
    let (v, n3) := freshprop n2 in
    --(v, (v |-> (fm', Iff (v, fm'))) defs2, n3)
    (v, () defs2, n3)
end

/-
(* Helper function for finding the next unsed prop variable index.

   It returns the max of `n` and the smallest non-negative integer `k` such
   that `str` is `prefix ^ suffix`, `suffix` represents an int, and
   `int_of_string suffix <= k`. `n` is the default
*)
let max_varindex prefix =
  let m = String.length prefix in
  fun str n ->
    let l = String.length str in
    if l <= m || String.sub str 0 m <> prefix then n
    else
      let s' = String.sub str m (l - m) in
      if List.for_all numeric (explode s') then Int.max n (int_of_string s')
      else n

let mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = 1 + overatoms (fun p n -> max_varindex "p_" (pname p) n) fm' 0 in
  let fm'', defs, _ = fn (fm', undefined, n) in
  let deflist = List.map (snd ** snd) (graph defs) in
  unions (simpcnf fm'' :: List.map simpcnf deflist)

let defcnf_sets fm = mk_defcnf defcnf_inner fm
let defcnf fm = list_conj (List.map list_disj (defcnf_sets fm))

end CNF
-/
-/
