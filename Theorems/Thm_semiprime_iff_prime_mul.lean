import Mathlib

/-! # Semiprimes are products of two primes

Published as `semiprime_iff_prime_mul` (prove2.me, theorem id
`267a9b9c-f6cc-44fe-8956-b9d436f36ac7`). Statement skeleton; the proof
lives in `Solutions/Sol_semiprime_iff_prime_mul.lean`. -/

open scoped ArithmeticFunction.Omega

theorem semiprime_iff_prime_mul (n : ℕ) :
    Nat.IsSemiprime n ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q := by
  constructor
  · intro h
    have h' : n ≠ 0 ∧ Ω n = 2 := h
    have hlen : Ω n = n.primeFactorsList.length := ArithmeticFunction.cardFactors_apply
    rw [hlen] at h'
    have hl : n.primeFactorsList.length = 2 := h'.2
    rcases List.length_eq_two.1 hl with ⟨p, q, hpq⟩
    refine ⟨p, q, ?_, ?_, ?_⟩
    · have h1 : p ∈ n.primeFactorsList := by rw [hpq]; exact List.Mem.head _
      exact Nat.prime_of_mem_primeFactorsList h1
    · have h2 : q ∈ n.primeFactorsList := by rw [hpq]; exact List.Mem.tail _ (List.Mem.head _)
      exact Nat.prime_of_mem_primeFactorsList h2
    · have hprod := Nat.prod_primeFactorsList h'.1
      rw [hpq] at hprod
      simpa using hprod.symm
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact Nat.Prime.mul_isAlmostPrime_two hp hq
