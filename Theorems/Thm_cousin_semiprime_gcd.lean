import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Two distinct cousin semiprimes are coprime unless they are 21 and 77

Published as `cousin_semiprime_gcd` (prove2.me, theorem id
`b5f31bd0-254d-4f85-9129-3abf75a523e8`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_gcd.lean`. -/

theorem cousin_semiprime_gcd (m n : ℕ) (hm : IsCousinSemiprime m)
    (hn : IsCousinSemiprime n) (hmn : m ≠ n) :
    m.Coprime n ∨ {m, n} = ({21, 77} : Finset ℕ) := by
  sorry
