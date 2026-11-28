import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_divisors
import Theorems.Thm_gap_semiprime_four_iff

/-! # A cousin semiprime has exactly four divisors

Published as `cousin_semiprime_divisors_card` (prove2.me, theorem id
`b5ca1856-4e1d-55a2-8826-256f295b98ec`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_divisors_card.lean`. -/

theorem cousin_semiprime_divisors_card (n : ℕ) (h : IsCousinSemiprime n) :
    (Nat.divisors n).card = 4 := by
  obtain ⟨p, hp, hq, rfl, hd⟩ :=
    gap_semiprime_divisors 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
  rw [hd]
  have hp2 : 2 ≤ p := hp.two_le
  have hgt : p < p * (p + 4) := by nlinarith [hp.two_le, Nat.zero_le p]
  have hgt2 : p + 4 < p * (p + 4) := by nlinarith [hp.two_le, Nat.zero_le p]
  have hne1 : (1:ℕ) ∉ ({p, p + 4, p * (p + 4)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hne2 : p ∉ ({p + 4, p * (p + 4)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hne3 : (p + 4) ∉ ({p * (p + 4)} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.card_insert_of_notMem hne1, Finset.card_insert_of_notMem hne2,
    Finset.card_insert_of_notMem hne3, Finset.card_singleton]
