import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # An Edenic semiprime is never a perfect number

Published as `edenic_semiprime_not_perfect` (prove2.me, theorem id
`d8b40990-98d0-5f7e-9a77-13a8aaa5384b`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_not_perfect.lean`. -/

theorem edenic_semiprime_not_perfect (n : ℕ) (h : IsEdenicSemiprime n) : ¬ Nat.Perfect n := by
  sorry
