import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # The Möbius function of an Edenic semiprime is 1

Published as `edenic_semiprime_moebius` (prove2.me, theorem id
`78444a99-7271-57f8-b716-2792f28a540a`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_moebius.lean`. -/

theorem edenic_semiprime_moebius (n : ℕ) (h : IsEdenicSemiprime n) :
    ArithmeticFunction.moebius n = 1 := by
  sorry
