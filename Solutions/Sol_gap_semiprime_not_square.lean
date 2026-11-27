import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_not_square
import Theorems.Thm_gap_semiprime_squarefree

theorem solution (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ¬∃ x, x ^ 2 = n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  rintro ⟨x, hx⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hsq : Squarefree (p * (p + k)) :=
    gap_semiprime_squarefree k _ hk ⟨p, hp, hq, rfl⟩
  have hx1 : IsUnit x := hsq x (by rw [← hx, pow_two])
  have hx' : x = 1 := Nat.isUnit_iff.mp hx1
  rw [hx', one_pow] at hx
  nlinarith [hp2, Nat.zero_le k]
