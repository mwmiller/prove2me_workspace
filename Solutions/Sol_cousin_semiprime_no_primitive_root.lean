import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_no_primitive_root

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ¬∃ g : ZMod n, IsPrimitiveRoot g (Nat.totient n) :=
  gap_semiprime_no_primitive_root 4 n (by norm_num) (by norm_num)
    ((gap_semiprime_four_iff n).mp h)
