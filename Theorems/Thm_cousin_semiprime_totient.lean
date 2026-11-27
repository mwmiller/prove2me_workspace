import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Euler's totient of a cousin semiprime

Published as `cousin_semiprime_totient` (prove2.me, theorem id
`254aa2e5-975d-41d7-82ca-e6b710b23974`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_totient.lean`. -/

theorem cousin_semiprime_totient (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      n.totient = (p - 1) * (p + 3) := by
  sorry
