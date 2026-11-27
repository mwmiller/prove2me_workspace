import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is never prime

Published as `gap_semiprime_not_prime` (prove2.me, theorem id
`7e969a47-b9db-5772-ab57-2bc11ec418d2`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_not_prime.lean`. -/

theorem gap_semiprime_not_prime (k n : ℕ) (h : IsGapSemiprime k n) : ¬n.Prime := by
  sorry
