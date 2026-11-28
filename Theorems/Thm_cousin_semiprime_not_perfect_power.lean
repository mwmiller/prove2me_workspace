import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_not_perfect_power

/-! # A cousin semiprime is never a perfect power

Published as `cousin_semiprime_not_perfect_power` (prove2.me, theorem id
`5bb8b89b-cdff-48f2-9918-9978502f1310`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_not_perfect_power.lean`. -/

theorem cousin_semiprime_not_perfect_power (n : ℕ) (h : IsCousinSemiprime n) :
    ¬∃ a m : ℕ, 2 ≤ m ∧ a ^ m = n :=
  gap_semiprime_not_perfect_power 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
