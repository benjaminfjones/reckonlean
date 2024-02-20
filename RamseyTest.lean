import ReckonLean.Dpll
import ReckonLean.Ramsey


/- Attempt to prove that R(s, t) = n using the given tuatology prover implementation -/
def prove_ramsey (taut_impl: PFormula -> Bool) (s t n: Nat): IO Unit := do
  let rs <- List.mapM
    (fun n => do
      let res := taut_impl (ramsey s t n)
      IO.println s!"*** s:={s}, t:={t}, n:={n}: {res} ***"
      pure res)
    (List.drop 1 $ List.range (n+1))
  if rs.reverse.head! then
    IO.println "Proved."
  else
    IO.println "Refuted."

def main : IO Unit := do

  let (s, t, n) := (3, 3, 6)
  IO.println "\nRamsey instance: prove R(3, 3) = 6"
  IO.println "=================================="

  IO.print "DP: "
  timeit "dp" $ prove_ramsey dptaut s t n

  IO.println "DPLL: "
  timeit "dpll" $ prove_ramsey dplltaut s t n

  IO.println "DPLI: "
  timeit "dpli" $ prove_ramsey dplitaut s t n

  IO.println "DPLB: "
  timeit "dplb" $ prove_ramsey dplbtaut s t n

  IO.println "DPLB': "
  timeit "dplb'" $ prove_ramsey dplb'taut s t n

  let (s, t, n) := (3, 4, 9)
  IO.println "\nRamsey instance: prove R(3, 4) = 9"
  IO.println "=================================="

  -- DP blows the stack at n=8
  -- IO.print "DP: "
  -- prove_ramsey dptaut s t n

  IO.println "DPLL: "
  timeit "dpll" $ prove_ramsey dplltaut s t n

  IO.println "DPLI: "
  timeit "dpli" $ prove_ramsey dplitaut s t n

  IO.println "DPLB: "
  timeit "dplb" $ prove_ramsey dplbtaut s t n

  -- suffers from learned clause explosion
  -- IO.println "DPLB': "
  -- timeit "dplb'" $ prove_ramsey dplb'taut s t n

/-
Ramsey instance: prove R(3, 3) = 6
==================================
DP: *** s:=3, t:=3, n:=1: false ***
*** s:=3, t:=3, n:=2: false ***
*** s:=3, t:=3, n:=3: false ***
*** s:=3, t:=3, n:=4: false ***
*** s:=3, t:=3, n:=5: false ***
*** s:=3, t:=3, n:=6: true ***
Proved.
dp 65.9ms

DPLL:
*** s:=3, t:=3, n:=1: false ***
*** s:=3, t:=3, n:=2: false ***
*** s:=3, t:=3, n:=3: false ***
*** s:=3, t:=3, n:=4: false ***
*** s:=3, t:=3, n:=5: false ***
*** s:=3, t:=3, n:=6: true ***
Proved.
dpll 2.68ms

DPLI:
*** s:=3, t:=3, n:=1: false ***
*** s:=3, t:=3, n:=2: false ***
*** s:=3, t:=3, n:=3: false ***
*** s:=3, t:=3, n:=4: false ***
*** s:=3, t:=3, n:=5: false ***
*** s:=3, t:=3, n:=6: true ***
Proved.
dpli 1.51ms

DPLB:
*** s:=3, t:=3, n:=1: false ***
*** s:=3, t:=3, n:=2: false ***
*** s:=3, t:=3, n:=3: false ***
*** s:=3, t:=3, n:=4: false ***
*** s:=3, t:=3, n:=5: false ***
*** s:=3, t:=3, n:=6: true ***
Proved.
dplb 1.58ms

DPLB':
*** s:=3, t:=3, n:=1: false ***
*** s:=3, t:=3, n:=2: false ***
*** s:=3, t:=3, n:=3: false ***
*** s:=3, t:=3, n:=4: false ***
*** s:=3, t:=3, n:=5: false ***
*** s:=3, t:=3, n:=6: true ***
Proved.
dplb' 1.6ms

Ramsey instance: prove R(3, 4) = 9
==================================
DPLL:
*** s:=3, t:=4, n:=1: false ***
*** s:=3, t:=4, n:=2: false ***
*** s:=3, t:=4, n:=3: false ***
*** s:=3, t:=4, n:=4: false ***
*** s:=3, t:=4, n:=5: false ***
*** s:=3, t:=4, n:=6: false ***
*** s:=3, t:=4, n:=7: false ***
*** s:=3, t:=4, n:=8: false ***
*** s:=3, t:=4, n:=9: true ***
Proved.
dpll 9.13s

DPLI:
*** s:=3, t:=4, n:=1: false ***
*** s:=3, t:=4, n:=2: false ***
*** s:=3, t:=4, n:=3: false ***
*** s:=3, t:=4, n:=4: false ***
*** s:=3, t:=4, n:=5: false ***
*** s:=3, t:=4, n:=6: false ***
*** s:=3, t:=4, n:=7: false ***
*** s:=3, t:=4, n:=8: false ***
*** s:=3, t:=4, n:=9: true ***
Proved.
dpli 25.5s

DPLB:
*** s:=3, t:=4, n:=1: false ***
*** s:=3, t:=4, n:=2: false ***
*** s:=3, t:=4, n:=3: false ***
*** s:=3, t:=4, n:=4: false ***
*** s:=3, t:=4, n:=5: false ***
*** s:=3, t:=4, n:=6: false ***
*** s:=3, t:=4, n:=7: false ***
*** s:=3, t:=4, n:=8: false ***
*** s:=3, t:=4, n:=9: true ***
Proved.
dplb 26.3s

-/
