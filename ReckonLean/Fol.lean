import ReckonLean.Common
import ReckonLean.Formulas
import ReckonLean.FPF
import ReckonLean.Parser
import ReckonLean.Prop

import Std.Data.List.Lemmas

open Formula

inductive Term where
-- variable: name
| Var : String → Term
-- function: name, arguments; semantics will be defined in terms of an interpretation
| Fn : String → List Term → Term
deriving BEq, Hashable, Inhabited, Repr
open Term

def Term.to_string : Term → String := term_to_string
where
  -- this decomposition leads to an automatic termination proof by mutual structural recursion
  term_to_string
    | Var x => x
    | Fn name [] => s!"{name}"
    | Fn name args => let arg_str := String.intercalate ", " (args_to_strings args)
                      s!"{name}({arg_str})"
  args_to_strings
    | [] => []
    | t :: ts => (term_to_string t) :: (args_to_strings ts)

instance : ToString Term where
  toString := Term.to_string

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
    if hl : List.all pred.toList symbolic && args.length == 2 then
      have h₂ : args.length = 2 := by simp_all
      have _ : 1 ≤ args.length := by rw [h₂]; simp_arith
      have _ : 2 ≤ args.length := by rw [h₂]; exact Nat.le_refl _
      s!"{args[0]} {pred} {args[1]}"
    else
      let arg_str := String.intercalate ", " (List.mapTR Term.to_string args)
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
      papply (fun args => Fn f args) (parse_bracketed (parse_list "," (parse_term vs)) ")") ("("::rest)
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
    else
      -- usually, this sub-parser is ok to fail and backtrack higher up
      -- dbg_trace "expected top-level relation: =, <, <=, ..."
      ParseResult.error

def parse_prefix_atom (vs: ctx) : parser (Formula Fol)
  | p::"("::")"::rest => [(Atom (Fol.mk p []), rest)]
  | p::"("::rest =>
    papply (fun args => Atom (Fol.mk p args)) (parse_bracketed (parse_list "," (parse_term vs)) ")") ("("::rest)
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
def is_or : Formula Fol → Bool
  | Formula.Or _ _ => true | _ => false
def is_quant : Formula Fol → Bool
  | Formula.Forall _ _ | Formula.Exists _ _ => true | _ => false
#guard is_or <|"(forall x. x < 2 ==> (x < 3)) ∨ false"|>
#guard is_or <|"(forall x. x < 3) ∨ false"|>
#guard is_or <|"(x < 2 ==> false) ∨ false"|>
#guard is_quant <|"forall x. (x = 0) ∨ (x = 1)"|>

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

mutual
def print_term (prec: Int) (t: Term) : String :=
  match t with
  | Var x => x
  | Fn "^" [t1, t2] => print_infix_term true false prec 24 "^" t1 t2
  | Fn "/" [t1, t2] => print_infix_term true true prec 22 "/" t1 t2
  | Fn "*" [t1, t2] => print_infix_term false true prec 20 "*" t1 t2
  | Fn "-" [t1, t2] => print_infix_term true true prec 18 "-" t1 t2
  | Fn "+" [t1, t2] => print_infix_term false true prec 16 "+" t1 t2
  | Fn "::" [t1, t2] => print_infix_term false false prec 14 "::" t1 t2
  | Fn f args => print_fargs f args

def print_infix_term (is_left: Bool) (pad: Bool) (parent_prec prec: Int) (sym: String) (t1 t2: Term) :=
  let lterm := print_term (if is_left then prec else prec + 1) t1
  let rterm := print_term (if is_left then prec + 1 else prec) t2
  let sep := if pad then " " else ""
  if parent_prec > prec then
    s!"({lterm}{sep}{sym}{sep}{rterm})"
  else
    s!"{lterm}{sep}{sym}{sep}{rterm}"

def print_fargs (f: String) (args: List Term) : String :=
  if args.isEmpty then
    f
  else
    let arg_str := String.intercalate ", " (List.mapTR Term.to_string args)
    s!"{f}({arg_str})"
end
decreasing_by sorry

/- Round trip a bunch of different terms -/
#guard print_term 0 <<|"(x + 1) + 2"|>> == "(x + 1) + 2"
#guard print_term 0 <<|"(x) + 2"|>> == "x + 2"
#guard print_term 0 <<|"(x * y)^2"|>> == "(x * y)^2"
#guard print_term 0 <<|"x^x^x"|>> == "x^x^x"
#guard print_term 0 <<|"x^x+1^x"|>> == "x^x + 1^x"
#guard print_term 0 <<|"f(y)"|>> == "f(y)"
#guard print_term 0 <<|"c(0,1)"|>> == "c(0, 1)"
#guard print_term 0 <<|"c() * x^f(y)"|>> == "c * x^f(y)"

/--
Print a first-order formula.

Equality and inequality predicates are printed infix style.
-/
def print_fol : Formula Fol → String :=
  print_formula (fun _ fol => print_atom fol)
where
  print_atom (fol: Fol) : String :=
    if _ : List.mem fol.pred ["=", "<", "<=", ">", ">="] && fol.args.length == 2 then
      have _ : 2 ≤ fol.args.length := by simp_all
      have _ : 1 < fol.args.length := by simp_all
      have _ : 0 < fol.args.length := by simp_all
      print_infix_term false true 12 12 fol.pred fol.args[0] fol.args[1]
    else
      print_fargs fol.pred fol.args

/- Simpler version, but results are not pretty -/
def print_fol' := print_formula (fun _ f => Fol.toString f)

#guard print_fol <|"(x < 2)"|> == "x < 2"
#guard print_fol (<|"forall x. (x = 0) ∨ (x = 1)"|>) == "forall x. x = 0 ∨ x = 1"

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


/-
Universally generalize a first-order formula by introducing universal
quantifiers for every free variable.
-/
def generalize (fm : Formula Fol) : Formula Fol := List.foldr mk_forall fm (free_vars fm)

#guard print_fol (generalize <|"(2 * t > s)"|>) ==
  "forall s t. 2 * t > s"
#guard print_fol (generalize <|"exists t. (2 * t > s)"|>) ==
  "forall s. exists t. 2 * t > s"
#guard print_fol (generalize <|"(forall t. P(t, z)) ==> exists w. P(w, z)"|>) ==
  "forall z. (forall t. P(t, z)) ==> (exists w. P(w, z))"

open FPF

def Term.height : Term → Nat
  | Var _ => 0
  | Fn f args =>
    match args with
    | [] => 1
    | a :: as => (Nat.max (a.height) (Fn f as).height) + 1

-- Note: the mutually recursive version of `tsubst` terminates by (mutual)
-- structural recursion.
mutual
def tsubst_list (sfn: Func String Term) : List Term → List Term
  | [] => []
  | a :: as => (tsubst sfn a) :: tsubst_list sfn as

def tsubst (sfn: Func String Term) : Term → Term
  | Var x => applyd sfn Var x
  | Fn f args => Fn f (tsubst_list sfn args)
end

-- subst s |-> x+1 producing a new term with a different free variable
#guard toString (tsubst ("s" |=> <<|"x+1"|>>) <<|"2 * t + s"|>>) == "+(*(2, t), +(x, 1))"
-- subst y |-> x+1, a no-op
#guard toString (tsubst ("y" |=> <<|"x+1"|>>) <<|"2 * t + s"|>>) == "+(*(2, t), s)"
#guard free_vars_term (tsubst ("s" |=> <<|"x+1"|>>) <<|"2 * t + s"|>>) == ["t", "x"]

def max_var_name : List String → Nat
  | [] => 0
  | v :: vs => Nat.max v.length (max_var_name vs)

/- Lemma used to prove termination of `variant` -/
theorem max_var_name_mem : ∀ (v: String), ∀ (vars: List String),
  v ∈ vars → v.length ≤ max_var_name vars := by
  intro v vars
  induction vars with
  | nil =>
    intro hm
    exact absurd hm (List.not_mem_nil v)
  | cons x xs ih =>
    intro h
    rw [List.mem_cons] at h
    cases h with
    | inl hvx =>
      unfold max_var_name
      conv => rhs; rw [← hvx]
      apply Nat.le_max_left
    | inr hvxs =>
      unfold max_var_name
      calc
        v.length ≤ max_var_name xs := ih hvxs
        _        ≤ Nat.max x.length (max_var_name xs) := by apply Nat.le_max_right

/- Produce a variant of `x` by adding primes until the variant doesn't occur in `xs` -/
def variant (x: String) (xs: List String) : String :=
  if _hm : List.mem x xs then let x' := s!"{x}'"; variant x' xs else x
termination_by variant x xs => max_var_name xs + 1 - x.length
decreasing_by
  simp_wf
  unfold List.mem List.contains at _hm  -- reduce to application of List.elem
  have h : x.length ≤ max_var_name xs := max_var_name_mem x xs (List.mem_of_elem_eq_true _hm)
  have hh : x.length < x'.length := calc
    x.length < x.length + 1 := Nat.lt_succ_self _
    _        = x'.length := by apply Eq.symm; apply List.length_append
  exact Nat.sub_lt_sub_left (Nat.lt_succ_of_le h) hh

#guard variant "x" ["z", "y"] == "x"
#guard variant "x" ["x", "y"] == "x'"
#guard variant "x" ["x", "x'", "y"] == "x''"

mutual
/-
Perform an abitrary term substitution on a formula quantified by `x`, alpha-converting variables as
needed so that they are not incorrectly captured.
-/
partial def substq (sfn: Func String Term) (quant: String → Formula Fol → Formula Fol) (x: String) (fm: Formula Fol) : Formula Fol :=
  -- is there a free variable `y ≠ x` in `fm` whose substitution term contains `x`? If so, we must rename `x`
  let x' := if let some _ := List.find?
    (fun y => List.mem x (free_vars_term (applyd sfn (fun _ => Var y) y)))
    (Set.subtract (free_vars fm) [x])
  then
    -- perform the whole term subst and collect all the resulting free variables, then make a suitable variant of `x` to
    -- quantify over
    variant x (free_vars (subst (FPF.undefine sfn x) fm))
  else
    x
  quant x' (subst ((x |-> Var x') sfn) fm)

/- Perform an arbitrary term substition in a first-order formula -/
partial def subst (sfn: Func String Term) : Formula Fol → Formula Fol
  | Formula.False => Formula.False
  | Formula.True => Formula.True
  | Formula.Atom r => Formula.Atom {r with args := List.mapTR (tsubst sfn) r.args}
  | Formula.Not p => Formula.Not (subst sfn p)
  | Formula.And p q => Formula.And (subst sfn p) (subst sfn q)
  | Formula.Or p q => Formula.Or (subst sfn p) (subst sfn q)
  | Formula.Imp p q => Formula.Imp (subst sfn p) (subst sfn q)
  | Formula.Iff p q => Formula.Iff (subst sfn p) (subst sfn q)
  | Formula.Forall x p => substq sfn mk_forall x p
  | Formula.Exists x p => substq sfn mk_exists x p
end

-- non-trivial replacement of `x` doesn't occur when no renaming is needed!
#guard print_fol (subst ("x" |=> Var "z") <|"forall x. (x = y)"|>) ==
  "forall x. x = y"
-- quantified `x` is α-renamed to `x'`
#guard print_fol (subst ("y" |=> Var "x") <|"forall x. (x = y)"|>) ==
  "forall x'. x' = x"
-- quantified `x` and `x'` are α-renamed to `x'`, `x''` (resp.)
#guard print_fol (subst ("y" |=> Var "x") <|"forall x x'. (x = y ==> x = x')"|>) ==
  "forall x' x''. x' = x ==> x' = x''"


/- ------------------------------------------------------------------------- -/
/- Prenex Normal Form                                                        -/
/- ------------------------------------------------------------------------- -/

def simplify1 (fm: Formula Fol) : Formula Fol :=
  match fm with
  -- remove redundant quantifiers
  | .Forall x p => if List.mem x (free_vars p) then fm else p
  | .Exists x p => if List.mem x (free_vars p) then fm else p
  | _ => psimplify1 fm

def simplify : Formula Fol → Formula Fol
  | .Not p => simplify1 (.Not (simplify p))
  | .And p q => simplify1 (.And (simplify p) (simplify q))
  | .Or p q => simplify1 (.Or (simplify p) (simplify q))
  | .Imp p q => simplify1 (.Imp (simplify p) (simplify q))
  | .Iff p q => simplify1 (.Iff (simplify p) (simplify q))
  | .Forall x p => simplify1 (.Forall x (simplify p))
  | .Exists x p => simplify1 (.Exists x (simplify p))
  | fm => fm

#guard print_fol (simplify <|"true ==> (p <=> (p <=> false))"|>) == "p <=> ~p"
#guard print_fol (simplify <|"exists x y z. P(x) ==> Q(z) ==> false"|>) ==
  "exists x z. P(x) ==> ~Q(z)"
#guard print_fol (simplify <|"(forall x y. P(x) ∨ (P(y) ∧ false)) ==> exists z. Q"|>) ==
  "(forall x. P(x)) ==> Q"
