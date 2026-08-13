module

public import HJOA3.SumToSum.ThreeTwo.EightLevelOne
import HJOA3.QChooseSqSum

/-!
# `ReducedEight`, split into two closed halves and one residual
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/--
`sqExp_toNat_succ_left` with the truncation written out, which is the form the exponents of
`eightD₁` and friends are in.
-/
private theorem sq_succ_left (a m : ℕ) :
    (a + 1) ^ 2 + m ^ 2 - (a + 1) * m + m = a ^ 2 + m ^ 2 - a * m + (2 * a + 1) := by
  have h := sqExp_toNat_succ_left a m
  rw [sqExp_toNat, sqExp_toNat] at h
  omega

/-- `sqExp_toNat_succ_succ` with the truncation written out. -/
private theorem sq_succ_succ (a m : ℕ) :
    (a + 1) ^ 2 + (m + 1) ^ 2 - (a + 1) * (m + 1) = a ^ 2 + m ^ 2 - a * m + a + m + 1 := by
  have h := sqExp_toNat_succ_succ a m
  rw [sqExp_toNat, sqExp_toNat] at h
  omega

/-- One `q`-Pascal step on a `qChooseSqSum`-shaped block, moving weight and level together. -/
theorem sum_sqExp_qChoose_succ {R : Type*} [CommSemiring R] (q : R) (a N B : ℕ) :
    ∑ k ∈ range (B + 1), q ^ ((a + 1) ^ 2 + k ^ 2 - (a + 1) * k) * qChoose q (1 + N) k =
      q ^ (2 * a + 1) * ∑ k ∈ range (B + 1), q ^ (a ^ 2 + k ^ 2 - a * k) * qChoose q N k +
        q ^ (a + 1) * ∑ k ∈ range B, q ^ (a ^ 2 + k ^ 2 - a * k + k) * qChoose q N k := by
  rw [Finset.sum_range_succ'
      (fun k ↦ q ^ ((a + 1) ^ 2 + k ^ 2 - (a + 1) * k) * qChoose q (1 + N) k) B,
    Finset.sum_range_succ' (fun k ↦ q ^ (a ^ 2 + k ^ 2 - a * k) * qChoose q N k) B]
  have hL : ∀ k ∈ range B,
      q ^ ((a + 1) ^ 2 + (k + 1) ^ 2 - (a + 1) * (k + 1)) * qChoose q (1 + N) (k + 1) =
        q ^ (a + 1 + (a ^ 2 + k ^ 2 - a * k + k)) * qChoose q N k +
          q ^ (2 * a + 1 + (a ^ 2 + (k + 1) ^ 2 - a * (k + 1))) * qChoose q N (k + 1) := by
    intro k _
    rw [show 1 + N = N + 1 from by omega, qChoose_succ_succ, mul_add]
    congr 1
    · rw [show (a + 1) ^ 2 + (k + 1) ^ 2 - (a + 1) * (k + 1)
        = a + 1 + (a ^ 2 + k ^ 2 - a * k + k) from by have := sq_succ_succ a k; omega]
    · rw [← mul_assoc, mul_comm (q ^ ((a + 1) ^ 2 + (k + 1) ^ 2 - (a + 1) * (k + 1))) (q ^ (k + 1)),
        ← pow_add, show k + 1 + ((a + 1) ^ 2 + (k + 1) ^ 2 - (a + 1) * (k + 1))
          = 2 * a + 1 + (a ^ 2 + (k + 1) ^ 2 - a * (k + 1)) from by
          have := sq_succ_left a (k + 1); omega]
  have hA : ∀ k ∈ range B, q ^ (a + 1) * (q ^ (a ^ 2 + k ^ 2 - a * k + k) * qChoose q N k) =
      q ^ (a + 1 + (a ^ 2 + k ^ 2 - a * k + k)) * qChoose q N k :=
    fun k _ ↦ by rw [← mul_assoc, ← pow_add]
  have hB : ∀ k ∈ range B, q ^ (2 * a + 1) *
      (q ^ (a ^ 2 + (k + 1) ^ 2 - a * (k + 1)) * qChoose q N (k + 1)) =
        q ^ (2 * a + 1 + (a ^ 2 + (k + 1) ^ 2 - a * (k + 1))) * qChoose q N (k + 1) :=
    fun k _ ↦ by rw [← mul_assoc, ← pow_add]
  rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib, qChoose_zero, qChoose_zero, mul_one, mul_one,
    mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl hA, Finset.sum_congr rfl hB,
    show q ^ ((a + 1) ^ 2 + 0 ^ 2 - (a + 1) * 0)
      = q ^ (2 * a + 1) * q ^ (a ^ 2 + 0 ^ 2 - a * 0) from by
      rw [← pow_add]
      congr 1
      have := sq_succ_left a 0
      omega]
  ring

/-- The common middle of the two sides. -/
noncomputable def eightPartA (r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ m₂ ∈ range (2 * r₂ + 3), ∑ m₁ ∈ range (2 * r₂ + 3),
    X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂) + (2 * r₂ + 1) + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁)) *
      qChoose X (r₂ + r₃) m₂ * qChoose X m₂ m₁

/-- The right-hand side's remainder. -/
noncomputable def eightPartB (r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ m₂ ∈ range (2 * r₂ + 3), ∑ m₁ ∈ range (2 * r₂ + 2),
    X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂) + (r₂ + 1) + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁ + m₁)) *
      qChoose X (r₂ + r₃) m₂ * qChoose X m₂ m₁

/-- `eightD₁`'s remainder. -/
noncomputable def eightRem (r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ m₁ ∈ range (2 * r₂ + 3), ∑ m₂ ∈ range (2 * r₂ + 2),
    X ^ (r₃ ^ 2 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) +
        ((r₂ + 1) ^ 2 + (m₂ + 1) ^ 2 - (r₂ + 1) * (m₂ + 1)))) *
      qChoose X (r₂ + r₃) m₂ * qChoose X (m₂ + 1) m₁

/-- `eightRHSInt` at level `r₁ = r₂ + 1`. -/
private theorem eightRHSInt_succ_eq (r₂ r₃ : ℕ) :
    eightRHSInt (r₂ + 1) r₂ r₃ =
      ∑ m₁ ∈ range (2 * r₂ + 3), ∑ m₂ ∈ range (2 * r₂ + 3),
        X ^ (r₃ ^ 2 + ((r₂ + 1) ^ 2 + m₁ ^ 2 - (r₂ + 1) * m₁ + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂))) *
          qChoose X (1 + m₂) m₁ * qChoose X (r₂ + r₃) m₂ := by
  rw [eightRHSInt, show 2 * (r₂ + 1) + 1 = 2 * r₂ + 3 from by omega,
    show r₂ + 1 - r₂ = 1 from by omega]

/-- The right-hand side splits. -/
theorem eightRHSInt_succ_eq_partA_add_partB (r₂ r₃ : ℕ) :
    eightRHSInt (r₂ + 1) r₂ r₃ = eightPartA r₂ r₃ + eightPartB r₂ r₃ := by
  rw [eightRHSInt_succ_eq, eightPartA, eightPartB, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m₂ _ ↦ ?_
  set C : ℤ[X] := X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂)) * qChoose X (r₂ + r₃) m₂ with hC
  have hLHS : ∑ m₁ ∈ range (2 * r₂ + 3),
      X ^ (r₃ ^ 2 + ((r₂ + 1) ^ 2 + m₁ ^ 2 - (r₂ + 1) * m₁ + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂))) *
          qChoose (X : ℤ[X]) (1 + m₂) m₁ * qChoose X (r₂ + r₃) m₂ =
        C * ∑ k ∈ range (2 * r₂ + 2 + 1),
          X ^ ((r₂ + 1) ^ 2 + k ^ 2 - (r₂ + 1) * k) * qChoose (X : ℤ[X]) (1 + m₂) k := by
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr (by norm_num) fun m₁ _ ↦ ?_
    rw [show r₃ ^ 2 + ((r₂ + 1) ^ 2 + m₁ ^ 2 - (r₂ + 1) * m₁ + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂))
      = r₃ ^ 2 + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂) + ((r₂ + 1) ^ 2 + m₁ ^ 2 - (r₂ + 1) * m₁) from by
      omega, pow_add]
    ring
  rw [hLHS, sum_sqExp_qChoose_succ, mul_add]
  congr 1
  · rw [Finset.mul_sum, Finset.mul_sum, show 2 * r₂ + 3 = 2 * r₂ + 2 + 1 from by omega]
    refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
    rw [hC, pow_add, pow_add]
    ring
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
    rw [hC, pow_add, pow_add]
    ring

/-- `eightD₁` splits. -/
theorem eightD₁_eq_partA_add_rem (r₂ r₃ : ℕ) :
    eightD₁ r₂ r₃ = eightPartA r₂ r₃ + eightRem r₂ r₃ := by
  rw [eightD₁, eightPartA, eightRem]
  rw [Finset.sum_comm (s := range (2 * r₂ + 3)) (t := range (2 * r₂ + 3))
    (f := fun m₁ m₂ ↦ X ^ (r₃ ^ 2 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) +
        ((r₂ + 1) ^ 2 + m₂ ^ 2 - (r₂ + 1) * m₂))) *
      qChoose X (r₂ + 1 + r₃) m₂ * qChoose X m₂ m₁)]
  rw [Finset.sum_comm (s := range (2 * r₂ + 3)) (t := range (2 * r₂ + 2))
    (f := fun m₁ m₂ ↦ X ^ (r₃ ^ 2 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) +
        ((r₂ + 1) ^ 2 + (m₂ + 1) ^ 2 - (r₂ + 1) * (m₂ + 1)))) *
      qChoose X (r₂ + r₃) m₂ * qChoose X (m₂ + 1) m₁)]
  rw [Finset.sum_range_succ' (fun m₂ ↦ ∑ m₁ ∈ range (2 * r₂ + 3),
      X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁ + ((r₂ + 1) ^ 2 + m₂ ^ 2 - (r₂ + 1) * m₂))) *
        qChoose (X : ℤ[X]) (r₂ + 1 + r₃) m₂ * qChoose X m₂ m₁) (2 * r₂ + 2),
    Finset.sum_range_succ' (fun m₂ ↦ ∑ m₁ ∈ range (2 * r₂ + 3),
      X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂) + (2 * r₂ + 1) + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁)) *
        qChoose (X : ℤ[X]) (r₂ + r₃) m₂ * qChoose X m₂ m₁) (2 * r₂ + 2)]
  have hzero : ∑ m₁ ∈ range (2 * r₂ + 3),
      X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁ + ((r₂ + 1) ^ 2 + 0 ^ 2 - (r₂ + 1) * 0))) *
          qChoose (X : ℤ[X]) (r₂ + 1 + r₃) 0 * qChoose X 0 m₁ =
        ∑ m₁ ∈ range (2 * r₂ + 3),
          X ^ (r₃ ^ 2 + (r₂ ^ 2 + 0 ^ 2 - r₂ * 0) + (2 * r₂ + 1) + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁)) *
            qChoose (X : ℤ[X]) (r₂ + r₃) 0 * qChoose X 0 m₁ := by
    refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
    rw [show r₃ ^ 2 + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁ + ((r₂ + 1) ^ 2 + 0 ^ 2 - (r₂ + 1) * 0))
      = r₃ ^ 2 + (r₂ ^ 2 + 0 ^ 2 - r₂ * 0) + (2 * r₂ + 1) + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) from by
      have := sq_succ_left r₂ 0
      omega, qChoose_zero, qChoose_zero]
  have htail : ∑ k ∈ range (2 * r₂ + 2), ∑ m₁ ∈ range (2 * r₂ + 3),
      X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁ +
          ((r₂ + 1) ^ 2 + (k + 1) ^ 2 - (r₂ + 1) * (k + 1)))) *
          qChoose (X : ℤ[X]) (r₂ + 1 + r₃) (k + 1) * qChoose X (k + 1) m₁ =
        (∑ k ∈ range (2 * r₂ + 2), ∑ m₁ ∈ range (2 * r₂ + 3),
          X ^ (r₃ ^ 2 + (r₂ ^ 2 + (k + 1) ^ 2 - r₂ * (k + 1)) + (2 * r₂ + 1) +
              (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁)) *
            qChoose (X : ℤ[X]) (r₂ + r₃) (k + 1) * qChoose X (k + 1) m₁) +
          ∑ k ∈ range (2 * r₂ + 2), ∑ m₁ ∈ range (2 * r₂ + 3),
            X ^ (r₃ ^ 2 + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁ +
                ((r₂ + 1) ^ 2 + (k + 1) ^ 2 - (r₂ + 1) * (k + 1)))) *
              qChoose (X : ℤ[X]) (r₂ + r₃) k * qChoose X (k + 1) m₁ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [show r₂ + 1 + r₃ = r₂ + r₃ + 1 from by omega, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
    rw [qChoose_succ_succ, show r₃ ^ 2 + (r₂ ^ 2 + (k + 1) ^ 2 - r₂ * (k + 1)) + (2 * r₂ + 1) +
        (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁)
      = r₃ ^ 2 + (r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁ +
          ((r₂ + 1) ^ 2 + (k + 1) ^ 2 - (r₂ + 1) * (k + 1))) + (k + 1) from by
      have := sq_succ_left r₂ (k + 1)
      omega, pow_add]
    ring
  rw [hzero, htail]
  ring

/-- The remaining residual identity at level `r₁ = r₂ + 1`. -/
def ResidualEight : Prop :=
  ∀ r₂ r₃ : ℕ, r₃ ≤ r₂ → eightRem r₂ r₃ - eightD₂ r₂ r₃ = eightPartB r₂ r₃

/-- `ResidualEight` implies `ReducedEight`. -/
theorem reducedEight_of_residual (h : ResidualEight) : ReducedEight := fun r₂ r₃ h₃ ↦ by
  rw [eightRHSInt_succ_eq_partA_add_partB, eightD₁_eq_partA_add_rem, ← h r₂ r₃ h₃]
  ring

/-- `ResidualEight` implies `BaseEight`. -/
theorem baseEight_of_residual (h : ResidualEight) : BaseEight :=
  baseEight_of_reduced (reducedEight_of_residual h)

end HJOA3.SumToSum.ThreeTwo
