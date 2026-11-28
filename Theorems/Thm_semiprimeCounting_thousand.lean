import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The semiprime counting function at 1000

Published as `semiprimeCounting_thousand` (prove2.me, theorem id
`a0a9c913-25d4-4be1-b076-7ef8a9d2cd8b`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_semiprimeCounting_thousand.lean`. -/

-- HELPERS_BEGIN
private theorem isSemiprime_iff {n : ℕ} :
    Nat.IsSemiprime n ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q := by
  constructor
  · rintro ⟨hne, hΩ⟩
    have hn1 : n ≠ 1 := fun h => by simp [h] at hΩ
    obtain ⟨p, hp, hpv⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨m, rfl⟩ := hpv
    have hm : m ≠ 0 := fun h => by simp [h] at hne
    have h1 : ArithmeticFunction.cardFactors p + ArithmeticFunction.cardFactors m = 2 := by
      rwa [← ArithmeticFunction.cardFactors_mul hp.ne_zero hm]
    have hp1 : ArithmeticFunction.cardFactors p = 1 :=
      ArithmeticFunction.cardFactors_apply_prime hp
    have h2 : ArithmeticFunction.cardFactors m = 1 := by omega
    exact ⟨p, m, hp, ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h2, rfl⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact hp.mul_isAlmostPrime_two hq

/-- Semiprimality test for `n ≤ 1000`: a semiprime `n = p * q` with `p ≤ q` has
`p ≤ √n ≤ 31`, so it suffices to scan the range up to 31. Divisibility is checked
first because it is cheap, so the `Nat.Prime` checks only run when `p ∣ n`. -/
private def semiprimeCheck (n : ℕ) : Bool :=
  (List.range 32).any fun p =>
    decide (p ∣ n) && decide (Nat.Prime p) && decide (Nat.Prime (n / p))

private theorem semiprimeCheck_iff {n : ℕ} (hn : n ≤ 1000) :
    (semiprimeCheck n = true) ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q := by
  constructor
  · intro h
    simp only [semiprimeCheck, List.any_eq_true, List.mem_range] at h
    obtain ⟨p, _, he⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨hdvd, hp'⟩, hq'⟩ := he
    exact ⟨p, n / p, hp', hq', (Nat.mul_div_cancel' hdvd).symm⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    rw [semiprimeCheck, List.any_eq_true]
    rcases Nat.le_total p q with hle | hle
    · have hpp : p * p ≤ 1000 := le_trans (Nat.mul_le_mul_left p hle) hn
      have h31 : p ≤ 31 := by
        by_contra h
        have h32 : (32 : ℕ) ≤ p := Nat.succ_le_of_lt (Nat.not_le.mp h)
        exact absurd (le_trans (Nat.mul_le_mul_right p h32) hpp) (by omega)
      refine ⟨p, List.mem_range.mpr (Nat.lt_succ_of_le h31), ?_⟩
      rw [Nat.mul_div_cancel_left q hp.pos]
      simp [hp, hq, Nat.dvd_mul_right p q]
    · have hpq : q * p ≤ 1000 := by rwa [Nat.mul_comm] at hn
      have hqq : q * q ≤ 1000 := le_trans (Nat.mul_le_mul_left q hle) hpq
      have h31 : q ≤ 31 := by
        by_contra h
        have h32 : (32 : ℕ) ≤ q := Nat.succ_le_of_lt (Nat.not_le.mp h)
        exact absurd (le_trans (Nat.mul_le_mul_right q h32) hqq) (by omega)
      refine ⟨q, List.mem_range.mpr (Nat.lt_succ_of_le h31), ?_⟩
      rw [Nat.mul_comm p q, Nat.mul_div_cancel_left p hq.pos]
      simp [hp, hq, Nat.dvd_mul_right q p]
-- HELPERS_END

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem semiprimeCounting_thousand : semiprimeCounting 1000 = 299 := by
  simp only [semiprimeCounting]
  have h : (Finset.range 1001).filter Nat.IsSemiprime =
      (Finset.range 1001).filter (fun n => semiprimeCheck n = true) := by
    refine Finset.filter_congr fun n hn => ⟨fun h => ?_, fun h => ?_⟩
    · have hlt : n < 1001 := Finset.mem_range.mp hn
      have key : n ≤ 1000 := by omega
      exact (semiprimeCheck_iff key).mpr (isSemiprime_iff.mp h)
    · have hlt : n < 1001 := Finset.mem_range.mp hn
      have key : n ≤ 1000 := by omega
      exact isSemiprime_iff.mpr ((semiprimeCheck_iff key).mp h)
  rw [h]
  decide
