import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # Difference-of-squares representations of an Edenic semiprime

Published as `edenic_semiprime_diff_squares` (prove2.me, theorem id
`a0b0583d-34fa-56d4-8c06-78a0b72fa448`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_diff_squares.lean`. -/

theorem edenic_semiprime_diff_squares (n : ℕ) (h : IsEdenicSemiprime n) :
    ∀ u v, u ^ 2 - v ^ 2 = n → v = 1 ∨ (2 * u = n + 1 ∧ 2 * v = n - 1) := by
  sorry
