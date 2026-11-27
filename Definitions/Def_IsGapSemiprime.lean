import Mathlib

/-- A **gap semiprime** with gap `k` is a natural number that factors as the product of
two primes differing by exactly `k`:

`IsGapSemiprime k n ↔ ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k)`.

This is the gap-generalized umbrella predicate: `IsEdenicSemiprime n` is
`IsGapSemiprime 2 n` (twin primes), and `IsCousinSemiprime n` is `IsGapSemiprime 4 n`
(cousin primes). Most lemmas carry the side condition `k ≠ 0`, which excludes the square
case `n = p²` where the two prime factors coincide; parity of `k` decides the shape of
the family — for even `k > 0` both primes are odd (so `n` is odd, has no primitive
root modulo `n`, and `n ≡ 1 (mod 4)` iff `k ≡ 0 (mod 4)`), while for odd `k` one prime
must be `2` and `n = 2(2+k)`. -/
def IsGapSemiprime (k n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k)
