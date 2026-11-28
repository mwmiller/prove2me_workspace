import Mathlib

/-! # Consecutive twin primes are coprime

Published as `twin_primes_coprime` (prove2.me, theorem id
`2cb4c586-9f81-4183-9745-c253d78e2fc0`). Statement skeleton; the proof
lives in `Solutions/Sol_twin_primes_coprime.lean`. -/

theorem twin_primes_coprime (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) : p.Coprime (p + 2) := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have hdvd2 : p ∣ 2 := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · rw [h] at hp
    exact absurd hp Nat.not_prime_one
  · rw [h] at hp2
    exact absurd hp2 (by decide)
