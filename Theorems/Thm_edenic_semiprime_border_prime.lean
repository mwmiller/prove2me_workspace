import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # A prime divisor of an Edenic semiprime is a twin-pair border

Published as `edenic_semiprime_border_prime` (prove2.me, theorem id
`af8f7a1f-f7dc-5107-93b8-96a6108ec95e`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_border_prime.lean`. -/

theorem edenic_semiprime_border_prime (n q : ℕ) (h : IsEdenicSemiprime n)
    (hq : q.Prime) (hdvd : q ∣ n) :
    n = q * (q + 2) ∨ n = (q - 2) * q := by
  sorry
