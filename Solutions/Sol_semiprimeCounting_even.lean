import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun m => Nat.IsSemiprime m ∧ m % 2 = 0)).card =
      Nat.primeCounting (n / 2) := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (fun x => x / 2) ?_ ?_
    · intro x hx
      have hxr : x < n + 1 :=
        Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hxsp : Nat.IsSemiprime x ∧ x % 2 = 0 := (Finset.mem_filter.mp hx).2
      have hβ : (fun x => x / 2) x = x / 2 := rfl
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · have hne : x ≠ 0 := hxsp.1.1
        have hΩ : ArithmeticFunction.cardFactors x = 2 := hxsp.1.2
        have hx2 : x = 2 * (x / 2) := by omega
        have hx20 : x / 2 ≠ 0 := fun h => by omega
        have h2 : ArithmeticFunction.cardFactors (2:ℕ) = 1 :=
          ArithmeticFunction.cardFactors_apply_prime (by norm_num)
        rw [hx2] at hΩ
        rw [ArithmeticFunction.cardFactors_mul (by norm_num) hx20] at hΩ
        rw [h2] at hΩ
        have hΩ1 : ArithmeticFunction.cardFactors (x / 2) = 1 := by omega
        exact ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hΩ1
    · intro x hx y hy hxy
      have hx2 : x % 2 = 0 := (Finset.mem_filter.mp hx).2.2
      have hy2 : y % 2 = 0 := (Finset.mem_filter.mp hy).2.2
      have hxy' : x / 2 = y / 2 := hxy
      omega
  · refine Finset.card_le_card_of_injOn (fun y => 2 * y) ?_ ?_
    · intro y hy
      have hyr : y < n / 2 + 1 :=
        Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have hyp : Nat.Prime y := (Finset.mem_filter.mp hy).2
      have hβ : (fun y => 2 * y) y = 2 * y := rfl
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · exact ⟨Nat.Prime.mul_isAlmostPrime_two (by norm_num) hyp, by omega⟩
    · intro y₁ _hy₁ y₂ _hy₂ hxy
      have hxy' : 2 * y₁ = 2 * y₂ := hxy
      omega
