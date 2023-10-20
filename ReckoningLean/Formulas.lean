/-
(* ========================================================================= *)
(* Polymorphic type of formulas with parser and printer.                     *)
(* ========================================================================= *)
-/

import ReckoningLean.Common

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

#check Formula.Atom 0
/-
(*
 * General parsing of iterated infixes
 *
 *   Conventions:
 *   - opsym : string -- operator symbol
 *   - opcon : 'a formula * 'a formula -> 'a formula -- binary operator constructor
 *   - opupdate : ('a formula -> 'a formula) -> 'a formula -> 'a formula -> 'b
 *       where 'b is typically either 'a formula or an aggregate like ('a formula) list
 *   - sof : 'a formula -> 'b -- used in the opupdater to go from formulas to aggregates
 *   - subparser : parser -- parser of the infix operator's arguments
 *)
-/

abbrev token := String
abbrev tokens := List token
abbrev parser (a : Type) := tokens -> a × tokens

/- (* Parse a general infix operator, parametrized on the syntax, the constructor and the type and construction
   of the final AST.
-/
def parse_ginfix (opsym : token) (opupdate : (a -> b) -> a -> a -> b) (sof : a -> b) (subparser : parser a) (inp : tokens) : b × tokens :=
  let (e1, inp1) := subparser inp
  if inp1 != [] && List.head! inp1 == opsym then
    parse_ginfix opsym opupdate (opupdate sof e1) subparser (List.tail! inp1)
  else (sof e1, inp1)
termination_by parse_ginfix ops opu sof sub inp => List.length inp
decreasing_by
  simp_wf
  /- need proof that subparser consumes input -/
  sorry

def parse_right_infix (opsym : String) (opcon : a × a -> a) (subparser : parser a) : parser a :=
  parse_ginfix opsym (fun f e1 e2 => f (opcon (e1, e2))) id subparser

/-
(* Unsed for now

   let parse_left_infix opsym opcon =
     parse_ginfix opsym (fun f e1 e2 -> opcon (f e1, e2)) id

   let parse_list opsym =
     parse_ginfix opsym (fun f e1 e2 -> f e1 @ [ e2 ]) (fun x -> [ x ])
*)
-/

/-
(* ------------------------------------------------------------------------- *)
(* Other general parsing combinators.                                        *)
(* ------------------------------------------------------------------------- *)
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
(* Parsing of formulas, parametrized by atom parser "pfn".
 *
 *  Conventions:
    - type parser : string list -> 'a formula * string list
 *  - ifn : 'context -> parser for "infix atoms", e.g. in Fol these are atomic predicates like "x < 2" in "x < 2 /\ y > 1"
 *  - afn : 'context -> parser for general atoms, e.g. in Prop these are just propositional variables
 *  - vs  : 'context is the context (unused for now)
 *)
-/

/-
START HERE
def parse_atomic_formula iafn vs inp :=
  let ⟨ ifn, afn ⟩ := iafn
  match inp with
  | [] -> failwith "formula expected"
  | "false" :: rest -> (False, rest)
  | "true" :: rest -> (True, rest)
  | "(" :: rest -> (
      /- need to work around exceptions as control-flow -/
      try ifn vs inp
      with Failure _ -> parse_bracketed (parse_formula (ifn, afn) vs) ")" rest)
  | "~" :: rest ->
      papply (fun p -> Not p) (parse_atomic_formula (ifn, afn) vs rest)
  | "forall" :: x :: rest ->
      parse_quant (ifn, afn) (x :: vs) (fun (x, p) -> Forall (x, p)) x rest
  | "exists" :: x :: rest ->
      parse_quant (ifn, afn) (x :: vs) (fun (x, p) -> Exists (x, p)) x rest
  | _ -> afn vs inp

and parse_quant (ifn, afn) vs qcon x inp =
  match inp with
  | [] -> failwith "Body of quantified term expected"
  | y :: rest ->
      papply
        (fun fm -> qcon (x, fm))
        (if y = "." then parse_formula (ifn, afn) vs rest
         else parse_quant (ifn, afn) (y :: vs) qcon y rest)

and parse_formula (ifn, afn) vs inp =
  parse_right_infix "<=>"
    (fun (p, q) -> Iff (p, q))
    (parse_right_infix "==>"
       (fun (p, q) -> Imp (p, q))
       (parse_right_infix "\\/"
          (fun (p, q) -> Or (p, q))
          (parse_right_infix "/\\"
             (fun (p, q) -> And (p, q))
             (parse_atomic_formula (ifn, afn) vs))))
    inp

(* ------------------------------------------------------------------------- *)
(* Printing of formulas, parametrized by atom printer.                       *)
(* ------------------------------------------------------------------------- *)

let bracket p n f x y =
  if p then print_string "(" else ();
  Format.open_box n;
  f x y;
  Format.close_box ();
  if p then print_string ")" else ()

let rec strip_quant fm =
  match fm with
  | Forall (x, (Forall (_y, _p) as yp)) | Exists (x, (Exists (_y, _p) as yp)) ->
      let xs, q = strip_quant yp in
      (x :: xs, q)
  | Forall (x, p) | Exists (x, p) -> ([ x ], p)
  | _ -> ([], fm)

(* Print a formula given a (precision) printer for propositions *)
let print_formula pfn =
  let rec aux_print_formula pr fm =
    match fm with
    | False -> print_string "false"
    | True -> print_string "true"
    | Atom pargs -> pfn pr pargs
    | Not p -> bracket (pr > 10) 1 (print_prefix 10) "~" p
    | And (p, q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
    | Or (p, q) -> bracket (pr > 6) 0 (print_infix 6 "\\/") p q
    | Imp (p, q) -> bracket (pr > 4) 0 (print_infix 4 "==>") p q
    | Iff (p, q) -> bracket (pr > 2) 0 (print_infix 2 "<=>") p q
    | Forall (_x, _p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
    | Exists (_x, _p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
  and print_qnt qname (bvs, bod) =
    print_string qname;
    List.iter
      (fun v ->
        print_string " ";
        print_string v)
      bvs;
    print_string ". ";
    (* Format.print_space (); *)
    Format.open_box 0;
    aux_print_formula 0 bod;
    Format.close_box ()
  and print_prefix newpr sym p =
    print_string sym;
    aux_print_formula (newpr + 1) p
  and print_infix newpr sym p q =
    aux_print_formula (newpr + 1) p;
    print_string (" " ^ sym);
    (* Format.print_space (); *)
    print_string " ";
    aux_print_formula newpr q
  in
  aux_print_formula 0

let print_qformula pfn fm =
  Format.open_box 0;
  print_string "<<";
  Format.open_box 0;
  print_formula pfn fm;
  Format.close_box ();
  print_string ">>";
  Format.close_box ()

(* ------------------------------------------------------------------------- *)
(* Constructor Aliases                                                       *)
(* ------------------------------------------------------------------------- *)

let mk_not p = Not p
and mk_and p q = And (p, q)
and mk_or p q = Or (p, q)
and mk_imp p q = Imp (p, q)
and mk_iff p q = Iff (p, q)
and mk_forall x p = Forall (x, p)
and mk_exists x p = Exists (x, p)

(* ------------------------------------------------------------------------- *)
(* Destructors.                                                              *)
(* ------------------------------------------------------------------------- *)

let dest_iff fm =
  match fm with Iff (p, q) -> (p, q) | _ -> failwith "dest_iff"

let dest_and fm =
  match fm with And (p, q) -> (p, q) | _ -> failwith "dest_and"

let rec conjuncts fm =
  match fm with And (p, q) -> conjuncts p @ conjuncts q | _ -> [ fm ]

let dest_or fm = match fm with Or (p, q) -> (p, q) | _ -> failwith "dest_or"

let rec disjuncts fm =
  match fm with Or (p, q) -> disjuncts p @ disjuncts q | _ -> [ fm ]

let dest_imp fm =
  match fm with Imp (p, q) -> (p, q) | _ -> failwith "dest_imp"

(* More fine grained destructors for Imp *)
let antecedent fm = fst (dest_imp fm)
let consequent fm = snd (dest_imp fm)
-/

/-
(* ------------------------------------------------------------------------- *)
(* Apply a function to the atoms, otherwise keeping structure.               *)
(* ------------------------------------------------------------------------- *)
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

