import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_divisors

theorem solution (k n : ℕ) (_hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      n.divisors = {1, p, p + k, n} := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  refine ⟨p, hp, hq, rfl, ?_⟩
  rw [Nat.divisors_mul, Nat.Prime.divisors hp, Nat.Prime.divisors hq]
  ext x
  constructor <;> intro hx
  · rw [Finset.mem_mul] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h1 | h2 | h3 | h4
    · exact Finset.mem_mul.mpr ⟨1, by simp, 1, by simp, by simp [h1]⟩
    · exact Finset.mem_mul.mpr ⟨p, by simp, 1, by simp, by simp [h2]⟩
    · exact Finset.mem_mul.mpr ⟨1, by simp, p + k, by simp, by simp [h3]⟩
    · exact Finset.mem_mul.mpr ⟨p, by simp, p + k, by simp, by simp [h4]⟩
