import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Cousin semiprimes are 5 modulo 8

Published as `cousin_semiprime_mod_eight` (prove2.me, theorem id
`3f3b3518-6134-54a1-9dfb-0ea3f85172fe`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_mod_eight.lean`. -/

theorem cousin_semiprime_mod_eight (n : ℕ) (h : IsCousinSemiprime n) : n % 8 = 5 := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      exact absurd hq (by norm_num)
    · exact hodd
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases hp8 with h1 | h3 | h5 | h7
  · have hq8 : (p + 4) % 8 = 5 := by omega
    rw [Nat.mul_mod, h1, hq8]
  · have hq8 : (p + 4) % 8 = 7 := by omega
    rw [Nat.mul_mod, h3, hq8]
  · have hq8 : (p + 4) % 8 = 1 := by omega
    rw [Nat.mul_mod, h5, hq8]
  · have hq8 : (p + 4) % 8 = 3 := by omega
    rw [Nat.mul_mod, h7, hq8]
