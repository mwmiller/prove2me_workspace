import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_not_prime

/-! # A cousin semiprime is never prime

Published as `cousin_semiprime_not_prime` (prove2.me, theorem id
`7dce80a9-97a9-46d8-891d-275d49648721`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_not_prime.lean`. -/

theorem cousin_semiprime_not_prime (n : ℕ) (h : IsCousinSemiprime n) :
    ¬n.Prime :=
  gap_semiprime_not_prime 4 n ((gap_semiprime_four_iff n).mp h)
