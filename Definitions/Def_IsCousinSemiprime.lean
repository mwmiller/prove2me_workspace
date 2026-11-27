import Mathlib

/-- A **cousin semiprime** is a natural number that factors as the product of a
*cousin prime pair* — two primes differing by `4`:

`IsCousinSemiprime n ↔ ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4)`.

The smallest examples are `21 = 3 · 7` and `77 = 7 · 11`, which share the hinge prime
`7` — the only prime belonging to two cousin pairs, since a prime `r` in two cousin
pairs would make `r - 4, r, r + 4` an arithmetic progression of three primes, and
modulo `3` the only such progression is `(3, 7, 11)`. Every cousin semiprime is
`5 (mod 8)` (indeed `≡ 5 (mod 12)` except for `21`), is `4` less than a perfect square
`n + 4 = (p + 2)²`, and is a sum of two squares exactly when the lower prime is
`≡ 1 (mod 4)`. This is `IsGapSemiprime 4 n`, the gap-4 sibling of the Edenic
(twin-gap) family. -/
def IsCousinSemiprime (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4)
