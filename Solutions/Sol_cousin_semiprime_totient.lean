import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_totient

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      n.totient = (p - 1) * (p + 3) := by
  obtain ⟨p, hp, hq, rfl, htot⟩ :=
    gap_semiprime_totient 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
  refine ⟨p, hp, hq, rfl, ?_⟩
  rw [htot]
  have h : p + 4 - 1 = p + 3 := by omega
  rw [h]
