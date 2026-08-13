module

public import HJOA3.SumToSum.ThreeTwo.EightBlocks
import Mathlib.Tactic.Ring

/-!
# `RecEightRHS`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/-- The double sum satisfies §7's recurrence. -/
theorem recEightRHS : RecEightRHS := by
  intro r₁ r₂ r₃ hr₃₂ hr₂₁
  obtain ⟨D, rfl⟩ : ∃ D, r₁ = r₂ + D := ⟨r₁ - r₂, by omega⟩
  rw [eightRHS_eq_sum_tight (r₂ + D + 2) r₂ r₃ (by omega) hr₃₂,
    eightRHS_eq_sum_tight (r₂ + D) r₂ r₃ (by omega) hr₃₂,
    eightRHS_eq_sum_tight (r₂ + D + 1) (r₂ + 1) r₃ (by omega) (by omega),
    show r₂ + D + 2 - r₂ = D + 2 from by omega, show r₂ + D - r₂ = D from by omega,
    show r₂ + D + 1 - (r₂ + 1) = D from by omega,
    show r₂ + 1 + r₃ = r₂ + r₃ + 1 from by omega]
  have hker : ∀ b : ℕ,
      (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp r₂ b).toNat) * qChoose X (r₂ + r₃) b *
          qChooseSqSum X (D + 2 + b) (r₂ + D + 2) =
        X ^ (3 + 3 * (r₂ + D)) * (X ^ (r₃ ^ 2 + (sqExp r₂ b).toNat) * qChoose X (r₂ + r₃) b *
            qChooseSqSum X (D + b) (r₂ + D)) +
          (X ^ (2 + 2 * D) * (X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (b + 1)).toNat) *
              qChoose X (r₂ + r₃) b * qChooseSqSum X (D + b + 1) (r₂ + D + 1)) +
            X ^ (2 + 2 * D) * (X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) *
              qChoose X (r₂ + r₃) b * qChooseSqSum X (D + b) (r₂ + D + 1))) := by
    intro b
    have h₁ := sqExp_toNat_succ_left r₂ b
    have h₂ := sqExp_toNat_succ_succ r₂ b
    rw [show D + 2 + b = D + b + 2 from by omega, qChooseSqSum_kernel,
      show r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b
        = r₃ ^ 2 + (sqExp r₂ b).toNat + (2 * r₂ + 1) from by omega,
      show r₃ ^ 2 + (sqExp (r₂ + 1) (b + 1)).toNat
        = r₃ ^ 2 + (sqExp r₂ b).toNat + (r₂ + b + 1) from by omega]
    ring
  have hpad : ∑ b ∈ range (r₂ + r₃ + 1 + 1),
      (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) * qChoose X (r₂ + r₃) b *
          qChooseSqSum X (D + b) (r₂ + D + 1) =
      ∑ b ∈ range (r₂ + r₃ + 1),
        X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) * qChoose X (r₂ + r₃) b *
          qChooseSqSum X (D + b) (r₂ + D + 1) := by
    rw [Finset.sum_range_succ, qChoose_eq_zero_of_lt (by omega : r₂ + r₃ < r₂ + r₃ + 1), mul_zero,
      zero_mul, add_zero]
  have hgpeel : (∑ i ∈ range (r₂ + r₃ + 1),
        (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat + (i + 1)) *
          qChoose X (r₂ + r₃) (i + 1) *
          qChooseSqSum X (D + i + 1) (r₂ + D + 1)) +
      X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) 0).toNat + 0) * qChoose X (r₂ + r₃) 0 *
        qChooseSqSum X (D + 0) (r₂ + D + 1) =
      ∑ b ∈ range (r₂ + r₃ + 1),
        X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) * qChoose X (r₂ + r₃) b *
          qChooseSqSum X (D + b) (r₂ + D + 1) := by
    rw [← hpad]
    exact (Finset.sum_range_succ'
      (fun b ↦ (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) * qChoose X (r₂ + r₃) b *
        qChooseSqSum X (D + b) (r₂ + D + 1)) (r₂ + r₃ + 1)).symm
  have hst : ∀ i ∈ range (r₂ + r₃ + 1),
      (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat) * qChoose X (r₂ + r₃ + 1) (i + 1) *
          qChooseSqSum X (D + i + 1) (r₂ + D + 1) =
        X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat) * qChoose X (r₂ + r₃) i *
            qChooseSqSum X (D + i + 1) (r₂ + D + 1) +
          X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat + (i + 1)) * qChoose X (r₂ + r₃) (i + 1) *
            qChooseSqSum X (D + i + 1) (r₂ + D + 1) := by
    intro i _
    rw [qChoose_succ_succ, pow_add]
    ring
  have h0 : (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp (r₂ + 1) 0).toNat) * qChoose X (r₂ + r₃ + 1) 0 *
      qChooseSqSum X (D + 0) (r₂ + D + 1) =
      X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) 0).toNat + 0) * qChoose X (r₂ + r₃) 0 *
        qChooseSqSum X (D + 0) (r₂ + D + 1) := by
    simp
  have hsrc2 : ∑ b ∈ range (r₂ + r₃ + 1 + 1),
      (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat) * qChoose X (r₂ + r₃ + 1) b *
          qChooseSqSum X (D + b) (r₂ + D + 1) =
      (∑ b ∈ range (r₂ + r₃ + 1),
          X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (b + 1)).toNat) * qChoose X (r₂ + r₃) b *
            qChooseSqSum X (D + b + 1) (r₂ + D + 1)) +
        ∑ b ∈ range (r₂ + r₃ + 1),
          X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) * qChoose X (r₂ + r₃) b *
            qChooseSqSum X (D + b) (r₂ + D + 1) :=
    calc ∑ b ∈ range (r₂ + r₃ + 1 + 1),
          X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat) * qChoose X (r₂ + r₃ + 1) b *
            qChooseSqSum X (D + b) (r₂ + D + 1)
        = (∑ i ∈ range (r₂ + r₃ + 1),
              X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat) * qChoose X (r₂ + r₃ + 1) (i + 1) *
                qChooseSqSum X (D + i + 1) (r₂ + D + 1)) +
            X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) 0).toNat) * qChoose X (r₂ + r₃ + 1) 0 *
              qChooseSqSum X (D + 0) (r₂ + D + 1) :=
          Finset.sum_range_succ'
            (fun b ↦ (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat) *
              qChoose X (r₂ + r₃ + 1) b * qChooseSqSum X (D + b) (r₂ + D + 1)) (r₂ + r₃ + 1)
      _ = (∑ i ∈ range (r₂ + r₃ + 1),
              (X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat) * qChoose X (r₂ + r₃) i *
                  qChooseSqSum X (D + i + 1) (r₂ + D + 1) +
                X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat + (i + 1)) *
                  qChoose X (r₂ + r₃) (i + 1) * qChooseSqSum X (D + i + 1) (r₂ + D + 1))) +
            X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) 0).toNat + 0) * qChoose X (r₂ + r₃) 0 *
              qChooseSqSum X (D + 0) (r₂ + D + 1) := by
            rw [h0, Finset.sum_congr rfl hst]
      _ = (∑ i ∈ range (r₂ + r₃ + 1),
              X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat) * qChoose X (r₂ + r₃) i *
                qChooseSqSum X (D + i + 1) (r₂ + D + 1)) +
            ((∑ i ∈ range (r₂ + r₃ + 1),
                X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (i + 1)).toNat + (i + 1)) *
                  qChoose X (r₂ + r₃) (i + 1) * qChooseSqSum X (D + i + 1) (r₂ + D + 1)) +
              X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) 0).toNat + 0) * qChoose X (r₂ + r₃) 0 *
                qChooseSqSum X (D + 0) (r₂ + D + 1)) := by
            rw [Finset.sum_add_distrib]; ring
      _ = _ := by rw [hgpeel]
  have hlhs : ∑ b ∈ range (r₂ + r₃ + 1),
      (X : ℕ[X]) ^ (r₃ ^ 2 + (sqExp r₂ b).toNat) * qChoose X (r₂ + r₃) b *
          qChooseSqSum X (D + 2 + b) (r₂ + D + 2) =
      X ^ (3 + 3 * (r₂ + D)) * ∑ b ∈ range (r₂ + r₃ + 1),
          X ^ (r₃ ^ 2 + (sqExp r₂ b).toNat) * qChoose X (r₂ + r₃) b *
            qChooseSqSum X (D + b) (r₂ + D) +
        X ^ (2 + 2 * D) * ((∑ b ∈ range (r₂ + r₃ + 1),
            X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (b + 1)).toNat) * qChoose X (r₂ + r₃) b *
              qChooseSqSum X (D + b + 1) (r₂ + D + 1)) +
          ∑ b ∈ range (r₂ + r₃ + 1),
            X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) * qChoose X (r₂ + r₃) b *
              qChooseSqSum X (D + b) (r₂ + D + 1)) :=
    calc ∑ b ∈ range (r₂ + r₃ + 1),
          X ^ (r₃ ^ 2 + (sqExp r₂ b).toNat) * qChoose X (r₂ + r₃) b *
            qChooseSqSum X (D + 2 + b) (r₂ + D + 2)
        = ∑ b ∈ range (r₂ + r₃ + 1),
            (X ^ (3 + 3 * (r₂ + D)) * (X ^ (r₃ ^ 2 + (sqExp r₂ b).toNat) *
                qChoose X (r₂ + r₃) b * qChooseSqSum X (D + b) (r₂ + D)) +
              (X ^ (2 + 2 * D) * (X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) (b + 1)).toNat) *
                  qChoose X (r₂ + r₃) b * qChooseSqSum X (D + b + 1) (r₂ + D + 1)) +
                X ^ (2 + 2 * D) * (X ^ (r₃ ^ 2 + (sqExp (r₂ + 1) b).toNat + b) *
                  qChoose X (r₂ + r₃) b * qChooseSqSum X (D + b) (r₂ + D + 1)))) :=
          Finset.sum_congr rfl fun b _ ↦ hker b
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum, ← mul_add]
  rw [hsrc2, hlhs]

end HJOA3.SumToSum.ThreeTwo
