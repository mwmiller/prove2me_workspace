import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The first four cousin semiprimes

Published as `cousin_semiprime_first_examples` (prove2.me, theorem id
`f8578850-eff9-5f0e-b99b-36ac914c485d`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_first_examples.lean`. -/

theorem cousin_semiprime_first_examples :
    IsCousinSemiprime 21 ∧ IsCousinSemiprime 77 ∧
      IsCousinSemiprime 221 ∧ IsCousinSemiprime 437 := by
  refine ⟨⟨3, by norm_num, by norm_num, by norm_num⟩,
    ⟨7, by norm_num, by norm_num, by norm_num⟩,
    ⟨13, by norm_num, by norm_num, by norm_num⟩,
    ⟨19, by norm_num, by norm_num, by norm_num⟩⟩
