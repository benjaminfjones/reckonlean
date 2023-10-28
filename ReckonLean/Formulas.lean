/-
=========================================================================
Polymorphic type of formulas with parser and printer.
=========================================================================
-/

import Init.Data.Format.Basic
import ReckonLean.Common
import ReckonLean.Parser

open Std

/- First order logical formula paramterized by the type of propositions -/
inductive Formula a where
  | False
  | True
  | Atom (n : a)
  | Not (p : Formula a)
  | And (p q : Formula a)
  | Or (p q : Formula a)
  | Imp (p q : Formula a)
  | Iff (p q : Formula a)
  | Forall (v : String) (p : Formula a)
  | Exists (v : String) (p : Formula a)

instance [Inhabited α]: Inhabited (Formula α) where
  default := Formula.Atom default

protected def Formula.repr {α : Type} [Repr α] : Formula α → Nat → Format
    | Formula.False, _ => "false"
    | Formula.True, _ => "true"
    | Formula.Atom x, prec => reprPrec x prec
    | Formula.Not p, prec => Repr.addAppParen ("Not " ++ Formula.repr p max_prec) prec
    | Formula.And p q, prec =>
        Repr.addAppParen ("And " ++ Formula.repr p max_prec ++ Formula.repr q max_prec) prec
    | Formula.Or p q, prec =>
        Repr.addAppParen ("Or " ++ Formula.repr p max_prec ++ Formula.repr q max_prec) prec
    | Formula.Imp p q, prec =>
        Repr.addAppParen ("Imp " ++ Formula.repr p max_prec ++ Formula.repr q max_prec) prec
    | Formula.Iff p q, prec =>
        Repr.addAppParen ("Iff " ++ Formula.repr p max_prec ++ Formula.repr q max_prec) prec
    | Formula.Forall x p, prec =>
        Repr.addAppParen (s!"Forall {x}. " ++ Formula.repr p max_prec) prec
    | Formula.Exists x p, prec =>
        Repr.addAppParen (s!"Exists {x}. " ++ Formula.repr p max_prec) prec

instance [Repr α] : Repr (Formula α) where
  reprPrec := Formula.repr

/-
General parsing of iterated infixes

  Conventions:
  - opsym : string -- operator symbol
  - opcon : 'a formula'a formula -> 'a formula -- binary operator constructor
  - opupdate : ('a formula -> 'a formula) -> 'a formula -> 'a formula -> 'b
      where 'b is typically either 'a formula or an aggregate like ('a formula) list
  - sof : 'a formula -> 'b -- used in the opupdater to go from formulas to aggregates
  - subparser : parser -- parser of the infix operator's arguments
-/

/- Parse a general infix operator, parametrized on the syntax, the constructor
   and the type and construction of the final AST.
-/
mutual
partial def parse_ginfix [Inhabited α] [Inhabited β] (opsym : token) (opupdate : (α -> β) -> α -> α -> β) (sof : α -> β) (subparser : parser α) : parser β :=
  fun inp =>
    let (e1, inp1) := subparser inp
    if inp1 != [] && List.head! inp1 == opsym then
      parse_ginfix opsym opupdate (opupdate sof e1) subparser (List.tail! inp1)
    else (sof e1, inp1)
/-
termination_by parse_ginfix ops opu sof sub inp => List.length inp
decreasing_by
  simp_wf
  /- need proof that subparser consumes input -/
  sorry
-/

partial def parse_right_infix [Inhabited α] (opsym : String) (opcon : α → α -> α) (subparser : parser α) : parser α :=
  parse_ginfix opsym (fun f e1 e2 => f (opcon e1 e2)) id subparser
end

/-
Unsed for now

   let parse_left_infix opsym opcon =
     parse_ginfix opsym (fun f e1 e2 -> opcon (f e1, e2)) id

   let parse_list opsym =
     parse_ginfix opsym (fun f e1 e2 -> f e1 @ [ e2 ]) (fun x -> [ x ])

-/

/-
-------------------------------------------------------------------------
Other general parsing combinators.
-------------------------------------------------------------------------
-/

/- Apply a function to a parser result -/
def papply (f : a -> b) (r : a × tokens) : b × tokens := (f r.fst, r.snd)


/- Token `tok` is next in the input stream `inp` -/
def nextin (inp : tokens) (tok : token) : Bool := inp != [] && List.head! inp == tok

def parse_bracketed [Inhabited a] (subparser : parser a) (bra_tok : token) : parser a :=
  fun inp =>
    let subres := subparser inp
    if nextin subres.snd bra_tok then (subres.fst, List.tail! subres.snd)
    else panic! "Closing bracket expected"

/-
Parsing of formulas, parametrized by atom parser "pfn".

 Conventions:
 - ifn : context -> parser for "infix atoms", e.g. in Fol these are atomic predicates like "x < 2" in "x < 2 /\ y > 1"
 - afn : context -> parser for general atoms, e.g. in Prop these are just propositional variables
 - vs  : the context (unused for now)

 ifn/afn have result type Option α instead of just α to represent errors

-/

abbrev ctx : Type := List String

/-
`iafn_type` is a pair of parsers designed to support both the language of propositional logic
and fisrt order logic. The `fst` is the predicate parser (or something that panics), the `snd` is
the atomic proposition parser.
-/
abbrev iafn_type (α : Type) := (ctx → parser (Option (Formula α))) × (ctx → parser (Option (Formula α)))

mutual
def parse_atomic_formula [Inhabited α] (iafn : iafn_type α) (vs : ctx) : parser (Formula α) :=
  let ⟨ ifn, afn ⟩ := iafn
  fun inp =>
    match inp with
    | [] => panic! "formula expected"
    | "false" :: rest => (Formula.False, rest)
    | "true" :: rest => (Formula.True, rest)
    | "(" :: rest => (
        /- need to work around exceptions as control-flow -/
        match ifn vs inp with
        | (none, _) => parse_bracketed (parse_formula iafn vs) ")" rest
        | (some r, toks) => (r, toks))
    | "~" :: rest =>
        papply (fun p => Formula.Not p) (parse_atomic_formula (ifn, afn) vs rest)
    | "forall" :: x :: rest =>
        parse_quant iafn (x :: vs) (fun x p => Formula.Forall x p) x rest
    | "exists" :: x :: rest =>
        parse_quant iafn (x :: vs) (fun x p => Formula.Exists x p) x rest
    | _ => match afn vs inp with
           | (none, _) => panic! "parser_atomic_formula"
           | (some r, toks) => (r, toks)

def parse_quant [Inhabited α] (iafn : iafn_type α) (vs : ctx) (qcon : String → Formula α → Formula α) (x : String) : parser (Formula α) :=
  fun inp =>
  match inp with
  | [] => panic! "Body of quantified term expected"
  | y :: rest =>
      papply
        (fun fm => qcon x fm)
        (if y == "." then parse_formula iafn vs rest
         else parse_quant iafn (y :: vs) qcon y rest)

def parse_formula [Inhabited α] (iafn : iafn_type α) (vs : ctx) : parser (Formula α) :=
  parse_right_infix "<=>"
    (fun p q => Formula.Iff p q)
    (parse_right_infix "==>"
       (fun p q => Formula.Imp p q)
       (parse_right_infix "\\/"
          (fun p q => Formula.Or p q)
          (parse_right_infix "/\\"
             (fun p q => Formula.And p q)
             (parse_atomic_formula iafn vs))))
end
termination_by
  /- These are obviously bollocks -/
  parse_formula _ c => 0
  parse_quant _ c _ _ => 0
  parse_atomic_formula _ c => 0
decreasing_by
  sorry

/-
-------------------------------------------------------------------------
Printing of formulas, parametrized by atom printer.
-------------------------------------------------------------------------
-/

def bracket_binary (p : Bool) (f: Formula α → Formula α → String) (x y: Formula α) :=
  let opener := if p then "(" else ""
  let middle := f x y
  let closer := if p then ")" else ""
  s!"{opener}{middle}{closer}"

def bracket_unary (p : Bool) (f: Formula α → String) x :=
  let opener := if p then "(" else ""
  let middle := f x
  let closer := if p then ")" else ""
  s!"{opener}{middle}{closer}"

def bracket_str (p : Bool) (f: String → String) x :=
  let opener := if p then "(" else ""
  let middle := f x
  let closer := if p then ")" else ""
  s!"{opener}{middle}{closer}"

def strip_quant {α : Type} (fm : Formula α) : List String × Formula α :=
  match fm with
  | Formula.Forall x yp@(Formula.Forall _y _p) | Formula.Exists x yp@(Formula.Exists _y _p) =>
      let ⟨xs, q⟩ := strip_quant yp
      (x :: xs, q)
  | Formula.Forall x p | Formula.Exists x p => ([ x ], p)
  | _ => ([], fm)

/- Print a formula given a (precision) printer for propositions -/
  mutual
  variable (α : Type)
  partial def aux_print_formula (pr: Int) (pfn: Int → α → String) (fm: Formula α) : String :=
    match fm with
    | Formula.False => "false"
    | Formula.True => "true"
    | Formula.Atom pargs => pfn pr pargs
    | Formula.Not p => bracket_unary (pr > 10) (print_prefix pfn 10 "~") p
    | Formula.And p q => bracket_binary (pr > 8) (print_infix pfn 8 "/\\") p q
    | Formula.Or p q => bracket_binary (pr > 6) (print_infix pfn 6 "\\/") p q
    | Formula.Imp p q => bracket_binary (pr > 4) (print_infix pfn 4 "==>") p q
    | Formula.Iff p q => bracket_binary (pr > 2) (print_infix pfn 2 "<=>") p q
    | Formula.Forall _ _p =>
        let opener := if (pr > 0) then "(" else ""
        let middle := (print_qnt pfn "forall") (strip_quant fm)
        let closer := if (pr > 0) then ")" else ""
        s!"{opener}{middle}{closer}"
    | Formula.Exists _ _p =>
        let opener := if (pr > 0) then "(" else ""
        let middle := (print_qnt pfn "exists") (strip_quant fm)
        let closer := if (pr > 0) then ")" else ""
        s!"{opener}{middle}{closer}"

  partial def print_qnt (pfn: Int → α → String) (qname: String) (vsf: List String × Formula α) : String :=
    let vs_str := String.join $ List.map (fun v => s!" {v}") vsf.fst
    let last := aux_print_formula 0 pfn vsf.snd
    s!"{qname}{vs_str}. {last}"

  partial def print_prefix (pfn: Int → α → String) (newpr : Int) (sym : String) (p : Formula α) : String :=
    let s := aux_print_formula (newpr + 1) pfn p
    s!"{sym}{s}"

  partial def print_infix (pfn: Int → α → String) (newpr: Int) (sym: String) (p q: Formula α) : String :=
    let op1 := aux_print_formula (newpr + 1) pfn p
    let op2 := aux_print_formula newpr pfn q
    s!"{op1} {sym} {op2}"
end

def print_formula (pfn: Int → α → String) : Formula α → String :=
  aux_print_formula α 0 pfn

def print_qformula (pfn: Int → α → String) (fm: Formula α): String :=
  let fm_str := print_formula pfn fm
  s!"<<{fm_str}>>"

/-
-------------------------------------------------------------------------
Constructor Aliases
-------------------------------------------------------------------------
-/

def mk_not (p: Formula α) := Formula.Not p
def mk_and (p q: Formula α) := Formula.And p q
def mk_or (p q: Formula α) := Formula.Or p q
def mk_imp (p q: Formula α) := Formula.Imp p q
def mk_iff (p q: Formula α) := Formula.Iff p q
def mk_forall (x: String) (p: Formula α) := Formula.Forall x p
def mk_exists (x: String) (p: Formula α) := Formula.Exists x p

/-
-------------------------------------------------------------------------
Destructors.
-------------------------------------------------------------------------
-/

namespace Dest
variable (α : Type)
def dest_iff : Formula α → Option (Formula α × Formula α)
  | Formula.Iff p q => some (p, q)
  | _ => none

def dest_and : Formula α → Option (Formula α × Formula α)
  | Formula.And p q => some (p, q)
  | _ => none

def dest_or : Formula α → Option (Formula α × Formula α)
  | Formula.Or p q => some (p, q)
  | _ => none

def dest_imp : Formula α → Option (Formula α × Formula α)
  | Formula.Imp p q => some (p, q)
  | _ => none

def conjuncts : Formula α → List (Formula α)
  | Formula.And p q => List.append (conjuncts p) (conjuncts q)
  | fm => [ fm ]

def disjuncts : Formula α → List (Formula α)
  | Formula.Or p q => List.append (disjuncts p) (disjuncts q)
  | fm => [ fm ]

/- More fine grained destructors for Imp -/
def antecedent {β : Type} (fm: Formula β) : Option (Formula β) :=
  if let some pair := dest_imp β fm then pair.fst else none
def consequent {β : Type} (fm: Formula β) : Option (Formula β) :=
  if let some pair := dest_imp β fm then pair.snd else none

end Dest

/-
-------------------------------------------------------------------------
Apply a function to the atoms, otherwise keeping structure.
-------------------------------------------------------------------------
-/

def onatoms (f : α → Formula α) : Formula α → Formula α
  | Formula.Atom x => f x
  | Formula.Not p => Formula.Not (onatoms f p)
  | Formula.And p q => Formula.And (onatoms f p) (onatoms f q)
  | Formula.Or p q => Formula.Or (onatoms f p) (onatoms f q)
  | Formula.Imp p q => Formula.Imp (onatoms f p) (onatoms f q)
  | Formula.Iff p q => Formula.Iff (onatoms f p) (onatoms f q)
  | Formula.Forall x p => Formula.Forall x (onatoms f p)
  | Formula.Exists x p => Formula.Exists x (onatoms f p)
  | p => p

def overatoms (f : α → β → β) (fm : Formula α) (b : β) : β :=
  match fm with
  | Formula.Atom a => f a b
  | Formula.Not p => overatoms f p b
  | Formula.And p q | Formula.Or p q | Formula.Imp p q | Formula.Iff p q =>
      overatoms f p (overatoms f q b)
  | Formula.Forall _ p | Formula.Exists _ p => overatoms f p b
  | _ => b

/- TODO: add list sets -/
/-
def atom_union f fm := setify (overatoms (fun h t => f h @ t) fm [])
def atoms fm := atom_union (fun a => [ a ]) fm
-/
