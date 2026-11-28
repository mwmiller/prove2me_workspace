import Mathlib

/-! # Twin primes are odd

Published as `twin_primes_odd` (prove2.me, theorem id
`bbb160cf-4e70-4629-85d7-2b73c3827277`). Statement skeleton; the proof
lives in `Solutions/Sol_twin_primes_odd.lean`. -/

theorem twin_primes_odd (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) : Odd p ∧ Odd (p + 2) := by
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  refine ⟨⟨k, hk⟩, k + 1, ?_⟩
  omega
