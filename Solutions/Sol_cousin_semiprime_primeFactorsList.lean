import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_primeFactorsList
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_primeFactorsList

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      n.primeFactorsList = [p, p + 4] :=
  gap_semiprime_primeFactorsList 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
