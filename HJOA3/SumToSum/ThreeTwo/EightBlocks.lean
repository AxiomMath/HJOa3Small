module

public import HJOA3.QChooseSqSum
public import HJOA3.SumToSum.ThreeTwo.EightRec
import Mathlib.Tactic.Ring

/-!
# `eightRHS`'s inner block is `qChooseSqSum`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/-- `eightRHS`'s `m₁`-sum is `qChooseSqSum`. -/
theorem eightRHS_eq_qChooseSqSum (r₁ r₂ r₃ : ℕ) (hr₂₁ : r₂ ≤ r₁) (hr₃₂ : r₃ ≤ r₂) :
    eightRHS r₁ r₂ r₃ =
      ∑ m₂ ∈ range (2 * r₁ + 1),
        X ^ (r₃ ^ 2 + (sqExp r₂ m₂).toNat) * qChoose X (r₂ + r₃) m₂ *
          qChooseSqSum X (r₁ - r₂ + m₂) r₁ := by
  rw [eightRHS, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₂ hm₂ ↦ ?_
  simp only [mem_range] at hm₂
  by_cases hs : m₂ ≤ r₂ + r₃
  · rw [qChooseSqSum_eq_sum_range X (by omega : r₁ - r₂ + m₂ ≤ 2 * r₁) r₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
    rw [← sqExp_toNat r₁ m₁, ← sqExp_toNat r₂ m₂,
      show r₃ ^ 2 + ((sqExp r₁ m₁).toNat + (sqExp r₂ m₂).toNat)
        = r₃ ^ 2 + (sqExp r₂ m₂).toNat + (sqExp r₁ m₁).toNat from by ring, pow_add]
    ring
  · rw [qChoose_eq_zero_of_lt (by omega : r₂ + r₃ < m₂)]
    simp

theorem eightRHS_eq_sum_tight (r₁ r₂ r₃ : ℕ) (hr₂₁ : r₂ ≤ r₁) (hr₃₂ : r₃ ≤ r₂) :
    eightRHS r₁ r₂ r₃ =
      ∑ m₂ ∈ range (r₂ + r₃ + 1),
        X ^ (r₃ ^ 2 + (sqExp r₂ m₂).toNat) * qChoose X (r₂ + r₃) m₂ *
          qChooseSqSum X (r₁ - r₂ + m₂) r₁ := by
  have hsub : range (r₂ + r₃ + 1) ⊆ range (2 * r₁ + 1) := by
    intro m hm
    simp only [mem_range] at hm ⊢
    omega
  rw [eightRHS_eq_qChooseSqSum r₁ r₂ r₃ hr₂₁ hr₃₂]
  refine (Finset.sum_subset hsub ?_).symm
  intro m _ hm
  simp only [mem_range, not_lt] at hm
  have hlt : r₂ + r₃ < m := by omega
  rw [qChoose_eq_zero_of_lt hlt]
  ring

end HJOA3.SumToSum.ThreeTwo
