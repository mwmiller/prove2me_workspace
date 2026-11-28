import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_no_primitive_root

/-! # A cousin semiprime admits no primitive root

Published as `cousin_semiprime_no_primitive_root` (prove2.me, theorem id
`7fb1f224-fb94-4c3c-b773-00cc9f6a31cc`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_no_primitive_root.lean`. -/

theorem cousin_semiprime_no_primitive_root (n : ℕ) (h : IsCousinSemiprime n) :
    ¬∃ g : ZMod n, IsPrimitiveRoot g (Nat.totient n) :=
  gap_semiprime_no_primitive_root 4 n (by norm_num) (by norm_num)
    ((gap_semiprime_four_iff n).mp h)
