import Mathlib

/-! # Bertrand's postulate for semiprimes

Published as `semiprime_bertrand_postulate` (prove2.me, theorem id
`9acd9d28-e02a-450c-af9f-4e167201538d`). Statement skeleton; the proof
lives in `Solutions/Sol_semiprime_bertrand_postulate.lean`. -/

theorem semiprime_bertrand_postulate (n : ℕ) (hn : 2 ≤ n) :
    ∃ m : ℕ, n < m ∧ m ≤ 2 * n ∧ Nat.IsSemiprime m := by
  have hk0 : n / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hkp, hp2k⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) hk0
  refine ⟨2 * p, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact Nat.Prime.mul_isAlmostPrime_two (by norm_num) hp
