import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_primeFactorsList

/-! # The prime factor list of a cousin semiprime

Published as `cousin_semiprime_primeFactorsList` (prove2.me, theorem id
`015bf201-27fd-4db8-bdfe-4b59846d7d4a`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_primeFactorsList.lean`. -/

theorem cousin_semiprime_primeFactorsList (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      n.primeFactorsList = [p, p + 4] :=
  gap_semiprime_primeFactorsList 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
