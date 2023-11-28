import ReckonLean.Common
import ReckonLean.Formulas
import ReckonLean.Parser

open Formula

inductive Term where
-- variable: name
| Var : String → Term
-- function: name, arguments; semantics will be defined in terms of an interpretation
| Fn : String → List Term → Term
deriving Inhabited, Repr
open Term

/-! The type of atomic predicates in a First Order Logic -/
structure Fol where
  -- predicate name; semantics will be defined in terms of an interpretation
  pred : String
  -- predicate arguments
  args : List Term
deriving Inhabited, Repr

/- Trivial example of "x + y < z".                                           -/
#eval (Atom ⟨"<", [Fn "+" [Var "x", Var "y"], Var "z"]⟩ : Formula Fol)

/- Special case of applying a subfunction to the top *terms*. -/
def onformula (f: Term → Term) : Formula Fol → Formula Fol := onatoms
  (fun tp => Atom {tp with args := List.map f tp.args})

/- ------------------------------------------------------------------------- -/
/- Parsing of terms.                                                         -/
/- ------------------------------------------------------------------------- -/

/- Defines what strings correspond to constants in the language. Others can be
expressed as nullary functions, e.g. pi() -/
def is_const_name (s: String) : Bool := List.all s.toList numeric || s == "nil"

mutual
partial def parse_atomic_term (vs: ctx) (inp: tokens) : Term × tokens :=
  match inp with
  | [] => panic! "parser_atomic_term: term expected"
  | "("::rest => match parse_bracketed (parse_term vs) ")" rest with
    | (none, _) => panic! "parser_atomic_term: expected closing bracket"
    | (some res, toks) => (res, toks)
  | "-"::rest =>
        let neg_res := parse_atomic_term vs rest
        papply (fun t => Fn "-" [t]) neg_res
  | f::"("::")"::rest => (Fn f [], rest)
  | f::"("::rest =>
      let bra_res := match parse_bracketed (parse_list "," (parse_term vs)) ")" rest with
        | (none, _) => panic! "parser_atomic_term: expected closing bracket"
        | (some res, toks) => (res, toks)
      papply (fun args => Fn f args) bra_res
  | a::rest =>
      ((if is_const_name a && not (List.mem a vs) then Fn a [] else Var a), rest)

partial def parse_term (vs: ctx) (inp: tokens) : Term × tokens :=
  parse_right_infix "::" (fun e1 e2 => Fn "::" [e1, e2])
    (parse_right_infix "+" (fun e1 e2 => Fn "+" [e1, e2])
       (parse_left_infix "-" (fun e1 e2 => Fn "-" [e1, e2])
          (parse_right_infix "*" (fun e1 e2 => Fn "*" [e1, e2])
             (parse_left_infix "/" (fun e1 e2 => Fn "/" [e1, e2])
                (parse_left_infix "^" (fun e1 e2 => Fn "^" [e1, e2])
                   (parse_atomic_term vs)))))) inp
end

def parset : String → Term := make_parser (parse_term [])

/- ------------------------------------------------------------------------- -/
/- Parsing of formulas.                                                      -/
/- ------------------------------------------------------------------------- -/

-- XXX both parse_infix_atom and parse_term need to be able to fail gracefully and return none from here
def parse_infix_atom (vs: ctx) : parser (Option (Formula Fol)) :=
  fun inp =>
    let (tm, rest) := parse_term vs inp
    if let some _ := List.find? (nextin rest) ["=", "<", "<=", ">", ">="] then
          papply (fun tm' => some (Atom {pred := rest.head!, args := [tm, tm']}))
                 (parse_term vs rest.tail!)
    else (none, inp)

def parse_atom (vs: ctx) : parser (Option (Formula Fol)) :=
  fun inp =>
    match parse_infix_atom vs inp with
    | (some res, rest) => (res, rest)
    | (none, _) =>
      -- parse_infix_atom failed, so parse a prefix atom
      match inp with
      | p::"("::")"::rest => (some (Atom {pred := p, args := []}), rest)
      | p::"("::rest =>
          if let (some bra_res, toks) := parse_bracketed (parse_list "," (parse_term vs)) ")" rest then
            papply (fun args => some (Atom {pred := p, args})) (bra_res, toks)
          else
            panic! s!"parse_atom: failed at {inp}"

      | p::rest => if p != "(" then (some (Atom {pred := p, args := []}), rest) else (none, inp)
      | _ => (none, inp)

def parse := make_parser
  (parse_formula (parse_infix_atom, parse_atom) [])


/- New Lean syntax for parsing first order logic formulas. -/
declare_syntax_cat folf
syntax str : folf  -- string for parse
syntax "<|" folf "|>" : term
macro_rules
| `(<|$s:str|>) => `(parse $s)

/- New Lean syntax for parsing first order logic terms. -/
declare_syntax_cat folt
syntax str : folt  -- string for parse
syntax "<<|" folt "|>>" : term
macro_rules
| `(<<|$s:str|>>) => `(parset $s)

-- XXX these all panic because during atomic formula parsing, the infix parser panics, so we need
-- to handle errors rather than panic. This entails a bunch of changes to all the parser components
-- #eval <|"(forall x. x < 2 ==> (x < 3)) ∨ false"|>
-- #eval <|"(forall x. x < 3) ∨ false"|>
-- #eval <|"(x < 2 ==> false) ∨ false"|>

/-
Formula.Atom { pred := "<", args := [Term.Var "x", Term.Fn "2" []] }
-/
#eval <|"x < 2"|>

/-
Term.Fn "*" [Term.Fn "2" [], Term.Var "x"]
-/
#eval <<|"2 * x"|>>
#eval <<|"3"|>>
