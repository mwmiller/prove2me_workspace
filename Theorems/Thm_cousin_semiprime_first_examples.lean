import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The first four cousin semiprimes

Published as `cousin_semiprime_first_examples` (prove2.me, theorem id
`f8578850-eff9-5f0e-b99b-36ac914c485d`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_first_examples.lean`. -/

theorem cousin_semiprime_first_examples :
    IsCousinSemiprime 21 ∧ IsCousinSemiprime 77 ∧
      IsCousinSemiprime 221 ∧ IsCousinSemiprime 437 := by
  sorry
