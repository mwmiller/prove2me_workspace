import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_squarefree

/-! # A cousin semiprime is squarefree

Published as `cousin_semiprime_squarefree` (prove2.me, theorem id
`99c136b3-76fc-5d11-8e1c-e92fc25e51fc`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_squarefree.lean`. -/

theorem cousin_semiprime_squarefree (n : ℕ) (h : IsCousinSemiprime n) :
    Squarefree n :=
  gap_semiprime_squarefree 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
