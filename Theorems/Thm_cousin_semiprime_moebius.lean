import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_moebius

/-! # The Möbius function of a cousin semiprime is 1

Published as `cousin_semiprime_moebius` (prove2.me, theorem id
`80b290d2-02f9-5db4-a33b-d52b8333c56d`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_moebius.lean`. -/

theorem cousin_semiprime_moebius (n : ℕ) (h : IsCousinSemiprime n) :
    ArithmeticFunction.moebius n = 1 :=
  gap_semiprime_moebius 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
