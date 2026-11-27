import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Euler's totient of a gap semiprime

Published as `gap_semiprime_totient` (prove2.me, theorem id
`ab12609a-2ccd-5525-89ef-96b13bdff569`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_totient.lean`. -/

theorem gap_semiprime_totient (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      n.totient = (p - 1) * (p + k - 1) := by
  sorry
