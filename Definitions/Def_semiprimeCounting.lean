import Mathlib

/-- `Nat.IsSemiprime` is an `abbrev` over the opaque `Nat.IsAlmostPrime`, so instance
search cannot find a decidability instance for it on its own; this provides the missing
`DecidablePred` (the underlying check `n ≠ 0 ∧ Ω n = 2` is decidable, since
`Ω n = n.primeFactorsList.length` computes). -/
instance semiprimeCounting.decidableIsSemiprime : DecidablePred
    (fun n : ℕ => Nat.IsSemiprime n) := fun n => by
  show Decidable (n ≠ 0 ∧ ArithmeticFunction.cardFactors n = 2)
  infer_instance

/-- The **semiprime counting function** `semiprimeCounting n` (π₂(n)) counts the
semiprimes — natural numbers `m` with `Nat.IsSemiprime m`, i.e. `Ω m = 2` — at most
`n`, mirroring `Nat.primeCounting`:

`semiprimeCounting n = card { m ∈ range (n+1) | Nat.IsSemiprime m }`.

Even semiprimes at most `n` are exactly the numbers `2p` with `p` prime and
`2p ≤ n`, so their number is precisely `Nat.primeCounting (n / 2)`; this gives the
lower bound `Nat.primeCounting (n / 2) ≤ semiprimeCounting n`. The function is
monotone and unbounded (there are infinitely many semiprimes), so it tends to `atTop`
along `atTop`. Asymptotics (π₂(n) ~ n log log n / log n) require the prime number
theorem and are deliberately out of scope. -/
def semiprimeCounting (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Nat.IsSemiprime).card
