import ReckonLean.Common
import ReckonLean.Formulas

/- A type for atomic propositions -/
structure Prp where
  name: String
deriving Repr

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

/- Prop formula Printer -/
def print_propvar (_prec: Int) (p: Prp) := p.name
def print_prop_formula := print_qformula print_propvar

#eval  print_prop_formula (parse_prop_formula "forall p. p \\/ q") == "<<forall p. p \\/ q>>"
