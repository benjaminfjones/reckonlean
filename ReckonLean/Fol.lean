import ReckonLean.Common
import ReckonLean.Formulas
import ReckonLean.FPF
import ReckonLean.Parser

open Formula

inductive Term where
-- variable: name
| Var : String → Term
-- function: name, arguments; semantics will be defined in terms of an interpretation
| Fn : String → List Term → Term
deriving BEq, Hashable, Inhabited, Repr
open Term

def Term.toString : Term → String
  | Var x => x
  | Fn name [] => s!"{name}"
  | Fn name args => let arg_str := String.intercalate "," (List.mapTR Term.toString args)
                    s!"{name}({arg_str})"
  decreasing_by sorry  -- TODO get around structural recursion

instance : ToString Term where
  toString := Term.toString

/-! The type of atomic predicates in a First Order Logic -/
structure Fol where
  -- predicate name; semantics will be defined in terms of an interpretation
  pred : String
  -- predicate arguments
  args : List Term
deriving BEq, Inhabited, Repr

def Fol.toString : Fol → String
  | ⟨ pred, [] ⟩ => s!"{pred}"
  | ⟨ pred, args ⟩ =>
    let arg_str := String.intercalate ", " (List.mapTR Term.toString args)
    s!"{pred}({arg_str})"

instance : ToString Fol where
  toString := Fol.toString

/- Trivial example of "x + y < z" -/
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
| `(<|$s:str|>) => `(((parse $s).getD default))

/- New Lean syntax for parsing first order logic terms. -/
declare_syntax_cat folt
syntax str : folt  -- string for parse
syntax "<<|" folt "|>>" : term
macro_rules
| `(<<|$s:str|>>) => `(((parset $s).getD default))

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
#eval <|"forall x. (x = 0) ∨ (x = 1)"|>

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

/- Print a first-order formula. Predicates are printed infix style. -/
def print_fol := print_formula (fun _ f => Fol.toString f)

#guard print_fol <|"(x < 2)"|> == "<(x, 2)"
#guard print_fol (<|"forall x. (x = 0) ∨ (x = 1)"|>) == "forall x. =(x, 0) ∨ =(x, 1)"

/- ------------------------------------------------------------------------- -/
/- Semantics of First Order Logic                                            -/
/- ------------------------------------------------------------------------- -/

open FPF
open Formula

/--
Interpretation

* `domain` is the (finite) domain of terms
* `func` is a (partial) function evaluator; we're not worried about arity or incorrect length arg lists
* `pred` is a (partial) predicate evaluator
-/
structure Interp (α : Type) where
  domain : List α
  func : String → List α → α
  pred : String → List α → Bool

abbrev Valuation α := Func String α

partial def termval [Inhabited α] (m: Interp α) (v: Valuation α) : Term → α
  | Var x => apply! v x
  | Fn f args => m.func f (List.mapTR (termval m v) args)

def holds [Inhabited α] (m: Interp α) (v: Valuation α) : Formula Fol → Bool
  | .False => false
  | .True => true
  | .Atom r => m.pred r.pred (List.mapTR (termval m v) r.args)
  | .Not p => not (holds m v p)
  | .And p q => (holds m v p) && (holds m v q)
  | .Or p q => (holds m v p) || (holds m v q)
  | .Imp p q => not (holds m v p) || (holds m v q)
  | .Iff p q => (holds m v p) == (holds m v q)
  | .Forall x p => List.all m.domain (fun (a : α) => holds m ((x |-> a) v) p)
  | .Exists x p => List.any m.domain (fun (a : α) => holds m ((x |-> a) v) p)


/-
Example interpretations
-/

def bool_interp : Interp Bool := {
  domain := [false, true],
  func := (fun fn args =>
    match (fn, args) with
    | ("0", []) => false
    | ("1", []) => true
    | ("+", [x, y]) => not (x == y)
    | ("*", [x, y]) => x && y
    | _ => panic! "bool_interp: uninterpreted function")
  pred := (fun pn args =>
    match (pn, args) with
    | ("=", [x, y]) => x == y
    | _ => panic! "bool_interp: uninterpreted predicate"
  )
}

def mod_interp (n : Nat) : Interp Nat := {
  domain := List.range_from_nat 0 (n-1),
  func := (fun fn args =>
    match (fn, args) with
    | ("0", []) => 0
    | ("1", []) => 1 % n
    | ("+", [x, y]) => (x + y) % n
    | ("*", [x, y]) => (x * y) % n
    | _ => panic! "mod_interp: uninterpreted function")
  pred := (fun pn args =>
    match (pn, args) with
    | ("=", [x, y]) => x == y
    | _ => panic! "mod_interp: uninterpreted predicate"
  )
}

def everything_is_zero_or_one := <|"forall x. (x = 0) ∨ (x = 1)"|>
#guard holds bool_interp undefined everything_is_zero_or_one
#guard holds (mod_interp 2) undefined everything_is_zero_or_one
#guard not $ holds (mod_interp 3) undefined everything_is_zero_or_one

-- TODO: the final atomic predicate `x * y = 1` has to be parenthesized or else parsing fails and we get
-- `False`:
-- #eval <|"forall x. ~(x = 0) ==> exists y. x * y = 1"|>

def every_nonzero_has_an_inverse := <|"forall x. ~(x = 0) ==> exists y. (x * y = 1)"|>
#guard holds bool_interp undefined every_nonzero_has_an_inverse
#guard holds (mod_interp 2) undefined every_nonzero_has_an_inverse
#guard holds (mod_interp 3) undefined every_nonzero_has_an_inverse

/- Use the semantics of `mod_interp` to determine the prime numbers up to 45 -/
#guard List.filter
  (fun n => holds (mod_interp n) undefined every_nonzero_has_an_inverse)
  (List.range_from_nat 1 45) ==
  [1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]


/- The set of (free; they're all free!) variables in a term -/
partial def free_vars_term : Term → List String
  | Var x => [x]
  | Fn _ args => Set.unions (List.mapTR free_vars_term args)

/- The set of **all** variables in a formula -/
def vars : Formula Fol → List String
  | .False | .True => []
  | .Atom ⟨ _, args ⟩ => Set.unions (List.mapTR free_vars_term args)
  | .Not p => vars p
  | .And p q | .Or p q | .Imp p q | .Iff p q => Set.union (vars p) (vars q)
  | .Forall x p | .Exists x p => Set.insert x (vars p)

/- The set of **free** variables in a formula -/
def free_vars : Formula Fol → List String
  | .False | .True => []
  | .Atom ⟨ _, args ⟩ => Set.unions (List.mapTR free_vars_term args)
  | .Not p => free_vars p
  | .And p q | .Or p q | .Imp p q | .Iff p q => Set.union (free_vars p) (free_vars q)
  | .Forall x p | .Exists x p => Set.subtract (free_vars p) [x]

#guard free_vars_term <<|"2 * t + s"|>> == ["s", "t"]
#guard free_vars_term <<|"2 * 5 + 0"|>> == []  -- ground term
#guard vars <|"(2 * t > s)"|> == ["s", "t"]
#guard vars <|"exists t. (2 * t > s)"|> == ["s", "t"]
#guard free_vars <|"exists t. (2 * t > s)"|> == ["s"]
#guard free_vars <|"forall s. exists t. (2 * t > s)"|> == []  -- sentence
#guard free_vars <|"(forall x. 0 <= x) ==> (0 <= 5)"|> == []  -- sentence
#guard free_vars <|"(forall x. 0 <= x) ==> (0 <= a)"|> == ["a"]
