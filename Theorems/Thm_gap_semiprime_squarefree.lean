import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is squarefree

Published as `gap_semiprime_squarefree` (prove2.me, theorem id
`d7837ed6-ba45-43ce-a124-d9d263036f7a`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_squarefree.lean`. -/

theorem gap_semiprime_squarefree (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    Squarefree n := by
  sorry
