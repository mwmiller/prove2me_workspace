import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # An even-gap semiprime admits no primitive root

Published as `gap_semiprime_no_primitive_root` (prove2.me, theorem id
`38c955bb-b810-5b09-9dc0-682ee615caaf`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_no_primitive_root.lean`. -/

theorem gap_semiprime_no_primitive_root (k n : ℕ) (hk : k % 2 = 0) (hk0 : 0 < k)
    (h : IsGapSemiprime k n) :
    ¬∃ g : ZMod n, IsPrimitiveRoot g (Nat.totient n) := by
  sorry
