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
partial def parse_atomic_term (vs: ctx) : parser Term :=
fun inp => match inp with
  | [] => panic! "parser_atomic_term: term expected"
  | "(" :: _ => parse_bracketed (parse_term vs) ")" inp
  | "-" :: rest => papply (fun t => Fn "-" [t]) (parse_atomic_term vs) rest
  | f::"("::")"::rest => [(Fn f [], rest)]
  | f::"("::rest =>
      papply (fun args => Fn f args) (parse_bracketed (parse_list "," (parse_term vs)) ")") rest
  | a::rest =>
      [((if is_const_name a && not (List.mem a vs) then Fn a [] else Var a), rest)]

partial def parse_term (vs: ctx) : parser Term :=
  parse_right_infix "::" (fun e1 e2 => Fn "::" [e1, e2])
    (parse_right_infix "+" (fun e1 e2 => Fn "+" [e1, e2])
       (parse_left_infix "-" (fun e1 e2 => Fn "-" [e1, e2])
          (parse_right_infix "*" (fun e1 e2 => Fn "*" [e1, e2])
             (parse_left_infix "/" (fun e1 e2 => Fn "/" [e1, e2])
                (parse_left_infix "^" (fun e1 e2 => Fn "^" [e1, e2])
                   (parse_atomic_term vs))))))
end

def parset : String → Option Term := make_parser (parse_term [])

/- ------------------------------------------------------------------------- -/
/- Parsing of formulas.                                                      -/
/- ------------------------------------------------------------------------- -/

def parse_infix_atom (vs: ctx) : parser (Formula Fol) :=
  fun inp => do
    let (tm, rest) <- parse_term vs inp
    if let some _ := List.find? (nextin rest) ["=", "<", "<=", ">", ">="] then
          papply (fun tm' => (Atom {pred := rest.head!, args := [tm, tm']}))
                 (parse_term vs) rest.tail!
    else dbg_trace "expected top-level relation: =, <, <=, ..."; ParseResult.error

def parse_prefix_atom (vs: ctx) : parser (Formula Fol)
  | p::"("::")"::rest => [(Atom (Fol.mk p []), rest)]
  | p::"("::rest =>
    papply (fun args => Atom (Fol.mk p args)) (parse_bracketed (parse_list "," (parse_term vs)) ")") rest
  | p::rest =>
    if p != "(" then
      [(Atom (Fol.mk p []), rest)]
    else
      dbg_trace s!"parse_prefix_atom: unexpected '('"; ParseResult.error
  | inp => dbg_trace s!"parse_prefix_atom: unexpected input '{inp}'"; ParseResult.error

def parse_atom (vs: ctx) : parser (Formula Fol) :=
  d_choose (parse_infix_atom vs) (parse_prefix_atom vs)

def parse : String → Option (Formula Fol) := make_parser
  (parse_formula (parse_infix_atom, parse_atom) [])

/- New Lean syntax for parsing first order logic formulas. -/
declare_syntax_cat folf
syntax str : folf  -- string for parse
syntax "<|" folf "|>" : term
macro_rules
| `(<|$s:str|>) => `((parse $s).getD default)

/- New Lean syntax for parsing first order logic terms. -/
declare_syntax_cat folt
syntax str : folt  -- string for parse
syntax "<<|" folt "|>>" : term
macro_rules
| `(<<|$s:str|>>) => `((parset $s).getD default)

/- These examples panic'd the parser before refactoring to monadic combinator style -/
/-
Formula.Or
  (Formula.Forall
    "x"
    (Formula.Imp
      (Formula.Atom { pred := "<", args := [Term.Var "x", Term.Fn "2" []] })
      (Formula.Atom { pred := "<", args := [Term.Var "x", Term.Fn "3" []] })))
  (Formula.False)
-/
#eval <|"(forall x. x < 2 ==> (x < 3)) ∨ false"|>
#eval <|"(forall x. x < 3) ∨ false"|>
#eval <|"(x < 2 ==> false) ∨ false"|>

/-
Bare predicate needs to be parenthesized?

Formula.Atom { pred := "<", args := [Term.Var "x", Term.Fn "2" []] }
-/
#eval <|"(x < 2)"|>

/-
Term.Fn "*" [Term.Fn "2" [], Term.Var "x"]
-/
#eval <<|"2 * x"|>>
#eval <<|"3"|>>
