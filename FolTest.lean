import ReckonLean.Fol

/--
The "drinkers principle"; there exists a person `x` such that if `x` drinks then everyone does.
This is Pelletier no. 18:

In any given interpretation, either the consequent of the inner implication is always true, in
which case the formula holds, or there is some domain value `x` such that the antecedant is false,
and again the implication holds.
-/
def p18: Formula Fol := <|"exists x. forall y. P(x) ==> P(y)"|>
-- step by step through Gilmore
-- 1. there are no free variables, so generalization is a no-op
#guard print_fol (generalize p18) == "exists x. forall y. P(x) ==> P(y)"
-- 2. negation and skolemization leaves a quantifier-free formula we want to prove is unsat
def p18_to_check := skolemize (.Not (generalize p18))
#guard print_fol p18_to_check == "P(x) ∧ ~P(f_y(x))"
-- 3. the Herbrand universe is generated by a made up constant `c` and a single unary function `f_y`.
#guard herbfuncs p18_to_check == ([("c", 0)], [("f_y", 1)])
-- 4. Gilmore loop
--
--    Level 0 of the ground instance enumeration has only `P(c) ∧ ~P(f_y(c))`. The propositional atoms
--    here are `c` and `f_y(c)` and there are clear interpretations of `P` and `f_y` under which the
--    formula is SAT.
--
--    Level 1 of the enumeration yields `P(f_y(c)) ∧ ~P(f_y(f_y(c)))`, but then the conjunction of this
--    with level 0 is unsatisfiable because we have conjoined literals with different polarity:
--
--    `P(c) ∧ ~P(f_y(c)) ∧ P(f_y(c)) ∧ ~P(f_y(f_y(c)))`
--
-- Trace:
-- ======
--
-- 0 instances ground tried; 1 items in list
-- current conjunction: [[]]
-- ground instances tried: []
-- ground instances to go: []
--
-- 0 instances ground tried; 1 items in list
-- current conjunction: [[]]
-- ground instances tried: []
-- ground instances to go: [[c]]
--
-- 1 instances ground tried; 1 items in list
-- current conjunction: [[P(c), ~P(f_y(c))]]
-- ground instances tried: [[c]]
-- ground instances to go: []
--
-- 1 instances ground tried; 1 items in list
-- current conjunction: [[P(c), ~P(f_y(c))]]
-- ground instances tried: [[c]]
-- ground instances to go: [[f_y(c)]]
--
-- Assert that easy_validity_ex is valid and Gilmore required 2 ground instances to prove it.
-- #guard gilmore easy_unsat_ex == 2


-- Pelletier problem 24
def p24 :=
   <|"~(exists x. U(x) ∧ Q(x)) ∧
     (forall x. P(x) ==> Q(x) ∨ R(x)) ∧
     ~(exists x. P(x) ==> (exists x. Q(x))) ∧
     (forall x. Q(x) ∧ R(x) ==> U(x))
     ==> (exists x. P(x) ∧ R(x))"|>

-- #guard gilmore p24 == 1

def p35 :=
  <|"exists x y. P(x,y) ==> forall x y. P(x,y)"|>
def p35_to_check := skolemize (.Not (generalize p35))
#guard print_fol p35_to_check == "P(x, y) ∧ ~P(c_x, c_y)"

-- Pelletier problem no. 45
def p45 :=
  <|"(forall x. P(x) ∧ (forall y. G(y) ∧ H(x,y) ==> J(x,y)) ==> (forall y. G(y) ∧ H(x,y) ==> R(y))) ∧
  ~(exists y. L(y) ∧ R(y)) ∧
  (exists x. P(x) ∧ (forall y. H(x,y) ==> L(y)) ∧ (forall y. G(y) ∧ H(x,y) ==> J(x,y)))
  ==> (exists x. P(x) ∧ ~(exists y. G(y) ∧ H(x,y)))"|>
def p45_to_check := skolemize (.Not (generalize p45))
#guard (DNF.simpdnf p45_to_check).length == 90  -- TODO: XXX: check against handbook
-- The clausal repreentation of the formula to be checked agrees exactly with
-- Pelletier's translation of no. 45 to skolemized CNF
#guard print_fol_sets (CNF.simpcnf p45_to_check) ==
  [["G(f_y(x))", "R(y)", "~G(y)", "~H(x, y)", "~P(x)"],
   ["G(f_y'(x))", "~P(x)"],
   ["H(x, f_y(x))", "R(y)", "~G(y)", "~H(x, y)", "~P(x)"],
   ["H(x, f_y'(x))", "~P(x)"],
   ["J(c_x, x)", "~G(x)", "~H(c_x, x)"],
   ["L(x)", "~H(c_x, x)"],
   ["P(c_x)"],
   ["R(y)", "~G(y)", "~H(x, y)", "~J(x, f_y(x))", "~P(x)"],
   ["~L(x)", "~R(x)"]]


def test_cases : List (String × Formula Fol × String × (Formula Fol → Nat)) :=
  [
    ("p18", p18, "gilmore", gilmore),
    ("p24", p24, "gilmore", gilmore),
    ("p35", p35, "gilmore", gilmore),
    -- TODO: XXX: proving p45 currently overflows the stack
    ("p45", p45, "gilmore", gilmore),
  ]

def main : IO Unit := do
  List.forM test_cases (fun (name, fm, tester_name, tester) => do
    IO.println s!"Solving {name} ({tester_name})"
    let start <- IO.monoNanosNow
    let res := tester fm
    let end_ <- IO.monoNanosNow
    IO.println s!"Done: no. instances tried {res}. Duration {end_ - start} ns"
    )
