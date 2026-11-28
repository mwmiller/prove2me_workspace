import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_not_square

/-! # A cousin semiprime is never a perfect square

Published as `cousin_semiprime_not_square` (prove2.me, theorem id
`ff885af3-4742-5a49-95fc-2db53540e733`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_not_square.lean`. -/

theorem cousin_semiprime_not_square (n : ℕ) (h : IsCousinSemiprime n) :
    ¬∃ x, x ^ 2 = n :=
  gap_semiprime_not_square 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
