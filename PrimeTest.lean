import ReckonLean.Mult
import ReckonLean.Dpll

/- Prove or refute primality with the given tautology prover implementation. -/
def test_primes (prover: PFormula → Bool) (prover_name: String) (lower upper: Nat) : IO Unit := do
  _ <- List.mapM
    (fun n => timeit s!"{prover_name} prime {n}" (do
      -- store results in an IO.Ref to prevent the compiler from lifting the constant constant computation
      let dump <- IO.mkRef false
      ST.Ref.set dump (prover (prime n))
      let res <- ST.Ref.get dump
      IO.println s!"{prover_name} prime {n} result: {res}"
    ))
    (List.drop lower $ List.range (upper+1))

def main : IO Unit := do
  -- There are all fast, until they run out of stack
  -- e.g. dp prime 14 26.4m
  test_primes dptaut "dp" 1 15  -- DP blows the stack at n = 16

  -- dpll proves most of these in less than 1 second, n = 64 is an outlier
  -- dpll prime 64 result: false
  -- dpll prime 64 5.95s
  test_primes dplltaut "dpll" 1 64

  -- significantly faster than `dpll`
  -- dpli prime 64 876ms
  -- 5.03 s total
  test_primes dplitaut "dpli" 1 64

  -- 5.8 s total
  test_primes dplbtaut "dplb" 1 64

  -- 5.4 s total
  test_primes dplb'taut "dplb'" 1 64

  -- compare implementations on a larger prime
  -- dpli prime 101 result: true
  -- dpli prime 101 478ms
  test_primes dplitaut "dpli" 101 101
  -- dplb prime 101 result: true
  -- dplb prime 101 501ms
  test_primes dplbtaut "dplb" 101 101
  -- dplb' prime 101 result: true
  -- dplb' prime 101 444ms
  test_primes dplb'taut "dplb'" 101 101
