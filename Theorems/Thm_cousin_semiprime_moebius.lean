import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The Möbius function of a cousin semiprime is 1

Published as `cousin_semiprime_moebius` (prove2.me, theorem id
`80b290d2-02f9-5db4-a33b-d52b8333c56d`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_moebius.lean`. -/

theorem cousin_semiprime_moebius (n : ℕ) (h : IsCousinSemiprime n) :
    ArithmeticFunction.moebius n = 1 := by
  sorry
