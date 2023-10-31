import ReckonLean.Common
import ReckonLean.Formulas

/- A type for atomic propositions -/
structure Prp where
  name: String

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

#check <<"p /\\ q">>
#eval  <<"p /\\ r">>
#eval  <<"p /\\ (q \\/ (r ==> s))">>

/- Prop formula Printer -/
def print_propvar (_prec: Int) (p: Prp) := p.name
def print_prop_formula := print_qformula print_propvar

/-
Examples
-/

/- round trip -/
#eval print_prop_formula (<<"p /\\ q">>) == "<<p /\\ q>>"  -- true
/- `rfl` won't close this for some reason, the LHS fails to evaluate fully
set_option trace.profiler true
example : print_prop_formula <<"p /\\ q">> = "<<p /\\ q>>" := by rfl
-/

#eval print_prop_formula <<"forall p. p \\/ q">> == "<<forall p. p \\/ q>>"  -- true
#eval print_prop_formula << "forall p. (exists q. (p \\/ ~p) /\\ (p \\/ q))">> ==
   "<<forall p. exists q. (p \\/ ~p) /\\ (p \\/ q)>>"  -- true; different parentheses


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
#eval psimplify <<"(true ==> (x <=> false)) ==> ~(y \\/ false /\\ z)">>
/- <<~x ==> ~y>> -/
#eval print_prop_formula (psimplify <<"(true ==> (x <=> false)) ==> ~(y \\/ false /\\ z)">>)

/- <<true>> -/
#eval print_prop_formula (psimplify <<"((x ==> y) ==> true) \\/ ~false">>)

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
    | _ => fm
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
