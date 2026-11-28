import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_sum_divisors

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      ∑ d ∈ n.divisors, d = (p + 1) * (p + 5) := by
  obtain ⟨p, hp, hq, rfl, hsum⟩ :=
    gap_semiprime_sum_divisors 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
  refine ⟨p, hp, hq, rfl, ?_⟩
  rw [hsum]
