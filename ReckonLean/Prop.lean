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
example : print_prop_formula <<"p /\\ q">> = "<<p /\\ q>>" := by rfl
-/
#eval print_prop_formula <<"forall p. p \\/ q">> == "<<forall p. p \\/ q>>"  -- true
#eval print_prop_formula << "forall p. (exists q. (p \\/ ~p) /\\ (p \\/ q))">> ==
   "<<forall p. exists q. (p \\/ ~p) /\\ (p \\/ q)>>"  -- true; different parentheses
