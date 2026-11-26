import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # Minus one is not a square modulo an Edenic semiprime

Published as `edenic_semiprime_neg_one_nonresidue` (prove2.me, theorem id
`24386284-4032-4d8d-9a05-456c6922f649`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_neg_one_nonresidue.lean`. -/

theorem edenic_semiprime_neg_one_nonresidue (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ y : ZMod n, y ^ 2 = -1 := by
  sorry
