import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_sum_divisors

/-! # The sum-of-divisors of a cousin semiprime

Published as `cousin_semiprime_sum_divisors` (prove2.me, theorem id
`7f900f18-47c1-43ae-831c-93c234c4a183`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_sum_divisors.lean`. -/

theorem cousin_semiprime_sum_divisors (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      ∑ d ∈ n.divisors, d = (p + 1) * (p + 5) := by
  obtain ⟨p, hp, hq, rfl, hsum⟩ :=
    gap_semiprime_sum_divisors 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
  refine ⟨p, hp, hq, rfl, ?_⟩
  rw [hsum]
