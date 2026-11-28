import Mathlib

/-! # There are infinitely many semiprimes

Published as `semiprimes_infinite` (prove2.me, theorem id
`64ff2aa1-fe25-405f-8e31-f3d79fdc65de`). Statement skeleton; the proof
lives in `Solutions/Sol_semiprimes_infinite.lean`. -/

theorem semiprimes_infinite : {n : ℕ | Nat.IsSemiprime n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro a
  obtain ⟨p, hp, hlt⟩ : ∃ p, p.Prime ∧ a < p := by
    simpa using not_bddAbove_iff.1 Nat.not_bddAbove_setOfPred_prime a
  exact ⟨p ^ 2, Nat.Prime.sq_isAlmostPrime_two hp,
    by rw [pow_two]; nlinarith [hp.two_le]⟩
