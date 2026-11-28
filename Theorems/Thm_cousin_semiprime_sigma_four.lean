import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_sum_divisors

/-! # The sum-of-divisors of a cousin semiprime is 0 modulo 4

Published as `cousin_semiprime_sigma_four` (prove2.me, theorem id
`bceb39ff-0845-5917-a09f-11edc5d51c35`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_sigma_four.lean`. -/

theorem cousin_semiprime_sigma_four (n : ℕ) (h : IsCousinSemiprime n) :
    (∑ d ∈ n.divisors, d) % 4 = 0 := by
  obtain ⟨p, hp, hq, rfl, hσ⟩ := cousin_semiprime_sum_divisors n h
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      exact absurd hq (by norm_num)
    · exact hodd
  rw [hσ]
  have h2a : 2 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have h2b : 2 ∣ p + 5 := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨c, hc1⟩ := h2a
  obtain ⟨d, hd1⟩ := h2b
  have h4 : 4 ∣ (p + 1) * (p + 5) := ⟨c * d, by rw [hc1, hd1]; ring⟩
  exact Nat.dvd_iff_mod_eq_zero.mp h4
