import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Even-gap semiprimes are 1 mod 4 exactly when the gap is 0 mod 4

Published as `gap_semiprime_mod_four` (prove2.me, theorem id
`92d077c2-67c6-4113-abc2-6d2af6c3ec7e`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_mod_four.lean`. -/

theorem gap_semiprime_mod_four (k n : ℕ) (hk : k % 2 = 0) (hk0 : 0 < k)
    (h : IsGapSemiprime k n) : n % 4 = 1 ↔ k % 4 = 0 := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      have hk2 : (2 + k) % 2 = 0 := by omega
      rcases hq.eq_two_or_odd with h2' | hodd'
      · omega
      · omega
    · exact hodd
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hk4 : k % 4 = 0 ∨ k % 4 = 2 := by omega
  rcases hp4 with hp4 | hp4 <;> rcases hk4 with hk4 | hk4
  · have hsum : (p + k) % 4 = 1 := by omega
    rw [Nat.mul_mod, hp4, hsum, hk4]
    decide
  · have hsum : (p + k) % 4 = 3 := by omega
    rw [Nat.mul_mod, hp4, hsum, hk4]
    decide
  · have hsum : (p + k) % 4 = 3 := by omega
    rw [Nat.mul_mod, hp4, hsum, hk4]
    decide
  · have hsum : (p + k) % 4 = 1 := by omega
    rw [Nat.mul_mod, hp4, hsum, hk4]
    decide

/-! # Family B: cousin semiprimes, gap 4 (B1–B23) -/
