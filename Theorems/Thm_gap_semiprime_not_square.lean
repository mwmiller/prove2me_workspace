import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_squarefree

/-! # A gap semiprime is never a perfect square

Published as `gap_semiprime_not_square` (prove2.me, theorem id
`5f579cd8-9369-5b69-a4ea-1fa87a430157`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_not_square.lean`. -/

theorem gap_semiprime_not_square (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
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
