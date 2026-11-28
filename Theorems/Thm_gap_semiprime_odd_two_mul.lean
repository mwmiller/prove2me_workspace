import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # An odd-gap semiprime is twice 2 + k

Published as `gap_semiprime_odd_two_mul` (prove2.me, theorem id
`690d1062-1667-46e9-9b09-7e993d4182c9`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_odd_two_mul.lean`. -/

theorem gap_semiprime_odd_two_mul (k n : ℕ) (hk : k % 2 = 1)
    (h : IsGapSemiprime k n) : n = 2 * (2 + k) := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  rcases hp.eq_two_or_odd with h2 | hodd
  · rw [h2]
  · have hk2 : (p + k) % 2 = 0 := by omega
    rcases hq.eq_two_or_odd with h2' | hodd'
    · omega
    · omega
