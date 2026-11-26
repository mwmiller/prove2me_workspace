import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # An Edenic semiprime admits no primitive root

Published as `edenic_semiprime_no_primitive_root` (prove2.me, theorem id
`2ef7c506-7acb-5cbe-be57-9d9140559dfb`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_no_primitive_root.lean`. -/

theorem edenic_semiprime_no_primitive_root (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ g : ZMod n, IsPrimitiveRoot g (Nat.totient n) := by
  sorry
