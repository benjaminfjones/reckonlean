import Std.Tactic.GuardExpr

import ReckonLean.Fol
import ReckonLean.Dpll

open Term

/-
First-order unsatisfiability checking using Herbrand's Theorem.

A quantifier-free first-order formula is unsatisfiable iff. some finite
subset of its ground instances (in a Herbrand universe for P) is
(propositionally) unsatisfiable.

-/

/-- Function list: pairs of function name and arity -/
abbrev FnList := List (String × Nat)

/--
Return the list of constants and functions appearing in the formula, making up a new
constant for the Herbrand universe in case there are none.
-/
def herbfuncs (fm: Formula Fol) : FnList × FnList :=
  let (cns, fns) := List.partition (fun (_, a) => a == 0) (formula_funcs fm)
  ((if cns.isEmpty then [("c", 0)] else cns), fns)

-- one constant, one function
#guard herbfuncs <|"exists x. exists y. (x * y = 1)"|> == ([("1", 0)], [("*", 2)])
-- one made-up constant, one function
#guard herbfuncs <|"exists x y z. (x * y = z)"|> == ([("c", 0)], [("*", 2)])

mutual
/--
Generate ground terms involving in total `n` functions as well as all `m`-tuples
of such terms.
-/
partial def groundterms (consts: List Term) (funcs: List (String × Nat)) : Nat → List Term
  | 0 => consts
  | Nat.succ nfuncs =>
    List.foldl
      (fun tms (f, arity) =>
        (List.mapTR (fun args => Fn f args) (groundtuples consts funcs nfuncs arity)) ++ tms)
      []
      funcs

/--
Generate `m`-tuples of terms each of which involves `nfuncs` functions in total.
-/
partial def groundtuples (consts: List Term) (funcs: List (String × Nat)) (nfuncs m: Nat) : List (List Term) :=
  if m == 0 then
    (if nfuncs == 0 then [[]] else [])
  else
    -- for k ∈ [0, n-1], generate ground terms with k functions,
    -- then prepend with (m-1)-tuples of ground terms with (n-k)
    -- functions
    List.foldl
      (fun tms k =>
        -- have hkin : k ∈ List.range n := by sorry  -- not enough context here to prove this
        -- have hk : k < n  -- from k ≤ n - 1
        (List.all_pairs (fun h t => h :: t)
          (groundterms consts funcs k)
          (groundtuples consts funcs (nfuncs-k) (m-1))) ++ tms)
      []
      (List.range (nfuncs+1))
end

/- Several tests since groundterms/groundtuples is easy to get wrong. -/
#guard groundterms [Fn "c" []] [("f", 1)] 0 == [Fn "c" []]  -- single constant term
#guard let consts2 := [Fn "c" [], Fn "a" []]; groundterms consts2 [("f", 1)] 0 == consts2
#guard groundtuples [Fn "c" []] [("f", 1)] 0 1 == [[Fn "c" []]]  -- single 1-tuple [[c]]
#guard groundtuples [Fn "c" []] [("f", 1)] 1 1 == [[Fn "f" [Fn "c" []]]]  -- 1-tuples of 1 function total: [[f(c)]]
#guard groundterms [Fn "c" []] [("f", 1)] 1 == [Fn "f" [Fn "c" []]] -- terms with 1 function total[f(c)]
#guard groundterms [Fn "c" []] [("f", 1)] 2 == [Fn "f" [Fn "f" [Fn "c" []]]]  -- terms with 2 functions: [f(f(c))]
-- Three 2-tuples involving 2 function applications:
-- 1. [f(f(c)), c]
-- 2. [f(c), f(c)]
-- 3. [c, f(f(c))]
#guard groundtuples [Fn "c" []] [("f", 1)] 2 2 ==
  [[Fn "f" [Fn "f" [Fn "c" []]], Fn "c" []],
   [Fn "f" [Fn "c" []], Fn "f" [Fn "c" []]],
    [Fn "c" [], Fn "f" [Fn "f" [Fn "c" []]]]]
-- How many ways are there to form two additions with two distinct variables?
-- #additions: (#inner +) + const, const + (#inner +) times (two possibilities for `const`) times #inner
-- #inner additions: (x + y), (y + x), (x + x), (y + y)
-- ==> 2 x 2 x 4 == 16 ✓
#guard List.length (groundterms [Fn "x" [], Fn "y" []] [("+", 2)] 2)  == 16

/-
Mechanising Herbrand's theorem
-/

open DNF

-- print DNF or CNF formula sets specialized to Formula Fol
def print_fol_sets := List.map (List.map (print_qliteral (fun _ f => Fol.toString f)))

-- Instantiation function; replaces free vars w/ ground terms
abbrev InstFn := Formula Fol → Formula Fol
-- Modification function: substitues into the first argument (original formula w/ free vars) using
-- the instantiation function, then conjoins with third argument and uses distribution to get back to DNF.
abbrev ModFn := DNFFormula Fol → InstFn → DNFFormula Fol → DNFFormula Fol
-- Satisfiability test function
abbrev TestFn := DNFFormula Fol → Bool

/--
Generic loop for Herbrand universe exploration procedures. Note that this loop
does not terminate when `fl0` is satisfiable.
-/
partial def herbloop
    (mfn: ModFn)                  -- modification function for set of ground inst's
    (tfn: TestFn)                 -- satisfiability test to use
    (fl0: DNFFormula Fol)         -- original first-order formula
    (consts: List Term)           -- constant terms in the H universe for `fl0`
    (funcs: List (String × Nat))  -- function, arity pairs for building the H universe
    (fvs: List String)            -- free variables of `fl0`
    (n: Nat)                      -- current level of H being enumerated
    (fl: DNFFormula Fol)          -- current conjunction of ground instances
    (tried: List (List Term))     -- tuples of ground instances tried so far
    (tuples: List (List Term))    -- ground tuples of length `fvs.length` left to try
    : List (List Term) :=
  dbg_trace (
  if n == 0 && tuples.isEmpty then
    "Start"
  else
    s!"n={n}, |tried|={tried.length} ground instances tried; |fl| = {fl.length} disj/conj"
  )
  match tuples with
  | [] => let newtups := groundtuples consts funcs n fvs.length
          dbg_trace s!"  * generated {newtups.length} new ground instances to try; starting next level"
          herbloop mfn tfn fl0 consts funcs fvs (n+1) fl tried newtups
  | tup::tups =>
    let fl' := mfn fl0 (subst (FPF.from_lists fvs tup)) fl
    dbg_trace s!"  * conjoined new ground instances; |fl| : {fl.length} -> {fl'.length}"
    if not (tfn fl') then
      dbg_trace s!"  * determined set of ground instances is UNSAT"
      -- found an unsatisfiable set of ground instances!
      tup :: tried
    else
      -- mark `tup` as tried and continue using the new current conjunction of ground inst's
      dbg_trace s!"  * new set of ground instances is still SAT; continuing..."
      herbloop mfn tfn fl0 consts funcs fvs n fl' (tup::tried) tups


/--
Setup `herbloop` for the Gilmore procedure.

The formulas and ground instances are kept in disjunctive normal form and the
test function is the usual simplification + contradiction checker on DNF set-of-sets
representations.
-/
def gilmore_loop :=
  herbloop
    (fun djs0 ifn djs =>
      List.filterTR (non contra) (CNF.pure_distrib (Set.image (Set.image ifn) djs0) djs))
    (fun djs => djs != [])

/--
The Gilmore procedure for first-order **validity** checking.

The formula is universally generalized, negated, and then Skolemized to eliminate
existential quantifiers. We test the result for unsatisfiability by systematically
exploring sets of ground instances from the Herbrand universe for the Skolemized
formula.
-/
def gilmore (fm: Formula Fol) : Nat :=
  let sfm := skolemize (.Not (generalize fm))
  let fvs := free_vars sfm
  let (consts, funcs) := herbfuncs sfm
  let consts := Set.image (fun (c,_) => Fn c []) consts
  List.length $ gilmore_loop (DNF.simpdnf sfm) consts funcs fvs 0 [[]] [] []
