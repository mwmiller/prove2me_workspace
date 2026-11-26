import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # An Edenic semiprime is the hypotenuse of a Pythagorean triple

Published as `edenic_semiprime_hypotenuse` (prove2.me, theorem id
`3e14c885-763a-4fd9-beb3-9b5d28fd322f`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_hypotenuse.lean`. -/

theorem edenic_semiprime_hypotenuse (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = n ^ 2 := by
  sorry
