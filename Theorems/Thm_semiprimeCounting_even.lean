import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Even semiprimes below n are counted by primeCounting(n/2)

Published as `semiprimeCounting_even` (prove2.me, theorem id
`5f494643-4772-431a-8f6f-4301325dde2b`). Statement skeleton; the proof
lives in `Solutions/Sol_semiprimeCounting_even.lean`. -/

theorem semiprimeCounting_even (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun m => Nat.IsSemiprime m ∧ m % 2 = 0)).card =
      Nat.primeCounting (n / 2) := by
  sorry
