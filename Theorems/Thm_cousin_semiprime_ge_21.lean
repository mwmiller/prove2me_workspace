import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_ge_even

/-! # A cousin semiprime is at least 21

Published as `cousin_semiprime_ge_21` (prove2.me, theorem id
`26a5ec2b-8201-5bc5-b0c8-bc63ac0b8f87`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_ge_21.lean`. -/

theorem cousin_semiprime_ge_21 (n : ℕ) (h : IsCousinSemiprime n) : 21 ≤ n :=
  gap_semiprime_ge_even 4 n (by norm_num) (by norm_num) ((gap_semiprime_four_iff n).mp h)
