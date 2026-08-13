module

public import HJOA3.QChoosePascalSum
public import HJOA3.SumToSum.ThreeTwo.EightLevelOne

/-!
# `RecEightLHS`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/-- The `n₅` block of `eightLHS`, at fixed `(n₁, n₂, n₄)`. -/
noncomputable def eightN₅Sum (R s r₃ n₁ n₂ n₄ : ℕ) : ℕ[X] :=
  ∑ n₅ ∈ range (R + 1),
    X ^ (eightExp R s r₃ n₁ n₂ n₄ n₅).toNat *
      (if n₂ ≤ n₅ then qChoose X (R - n₂) (n₅ - n₂) else 0)

/--
The slice of `eightLHS` at fixed `n₂` — the three inert binders `(n₁, n₄, n₅)` absorbed, with
only the outer binomial `qbinom{s}{n₂}` left outside.
-/
noncomputable def eightSlice (R s r₃ n₂ : ℕ) : ℕ[X] :=
  ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
    qChoose X n₄ n₁ * qChoose X r₃ n₄ * eightN₅Sum R s r₃ n₁ n₂ n₄

/-- `eightLHS` is its outer binomial against its slices. -/
theorem eightLHS_eq_sum_slice (r₁ r₂ r₃ : ℕ) (h₂₁ : r₂ ≤ r₁) :
    eightLHS r₁ r₂ r₃ = ∑ n₂ ∈ range (r₂ + 1), qChoose X r₂ n₂ * eightSlice r₁ r₂ r₃ n₂ := by
  rw [eightLHS_eq_guarded r₁ r₂ r₃ h₂₁]
  refine Finset.sum_congr rfl fun n₂ _ ↦ ?_
  rw [eightSlice, Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n₁ _ ↦ ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n₄ _ ↦ ?_
  rw [eightN₅Sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n₅ _ ↦ ?_
  ring

/-- The recurrence, per slice — `RecEightLHS` with two of its four binders gone. -/
def KernEightPrime : Prop :=
  ∀ r₁ r₂ r₃ n₂ : ℕ, r₃ ≤ r₂ → r₂ ≤ r₁ → n₂ ≤ r₂ →
    eightSlice (r₁ + 2) r₂ r₃ n₂ =
      X ^ (3 + 3 * r₁) * eightSlice r₁ r₂ r₃ n₂ +
        X ^ (2 + 2 * (r₁ - r₂)) *
          (eightSlice (r₁ + 1) (r₂ + 1) r₃ n₂ +
            X ^ (r₂ - n₂) * eightSlice (r₁ + 1) (r₂ + 1) r₃ (n₂ + 1))

/-- `KernEightPrime` implies `RecEightLHS`. -/
theorem recEightLHS_of_kern (h : KernEightPrime) : RecEightLHS := by
  intro r₁ r₂ r₃ h₃₂ h₂₁
  rw [eightLHS_eq_sum_slice (r₁ + 2) r₂ r₃ (by omega), eightLHS_eq_sum_slice r₁ r₂ r₃ h₂₁,
    eightLHS_eq_sum_slice (r₁ + 1) (r₂ + 1) r₃ (by omega), sum_qChoose_succ_mul',
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n₂ hn₂ ↦ ?_
  simp only [Finset.mem_range] at hn₂
  rw [h r₁ r₂ r₃ n₂ h₃₂ h₂₁ (by omega)]
  ring

/-- A slice's inner double sum, flag-refactored. -/
noncomputable def eightFlagSlice (R s r₃ n₁ n₂ : ℕ) : ℕ[X] :=
  ∑ t ∈ range (r₃ - n₁ + 1), qChoose X (r₃ - n₁) t * eightN₅Sum R s r₃ n₁ n₂ (n₁ + t)

/-- A slice is its flag binomial against its flag sub-slices. -/
theorem eightSlice_eq_sum_flagSlice (R s r₃ n₂ : ℕ) :
    eightSlice R s r₃ n₂ =
      ∑ n₁ ∈ range (r₃ + 1), qChoose X r₃ n₁ * eightFlagSlice R s r₃ n₁ n₂ := by
  rw [eightSlice]
  refine Finset.sum_congr rfl fun n₁ hn₁ ↦ ?_
  simp only [Finset.mem_range] at hn₁
  have hsub : Finset.Ico n₁ (r₃ + 1) ⊆ range (r₃ + 1) :=
    fun x hx ↦ Finset.mem_range.2 (Finset.mem_Ico.1 hx).2
  have hzero : ∀ n₄ ∈ range (r₃ + 1), n₄ ∉ Finset.Ico n₁ (r₃ + 1) →
      qChoose (X : ℕ[X]) n₄ n₁ * qChoose X r₃ n₄ * eightN₅Sum R s r₃ n₁ n₂ n₄ = 0 := by
    intro n₄ h₄ h₄'
    simp only [Finset.mem_range] at h₄
    simp only [Finset.mem_Ico, not_and, not_lt] at h₄'
    rw [qChoose_eq_zero_of_lt (show n₄ < n₁ from by omega)]
    ring
  rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range,
    show r₃ + 1 - n₁ = r₃ - n₁ + 1 from by omega, eightFlagSlice, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [mul_comm (qChoose (X : ℕ[X]) (n₁ + t) n₁) (qChoose X r₃ (n₁ + t)),
    qChoose_mul_semiring X (show n₁ ≤ n₁ + t from by omega),
    show n₁ + t - n₁ = t from by omega]
  ring

/-- The recurrence, per flag sub-slice — `RecEightLHS` with all but two of its binders gone. -/
def KernEightN1 : Prop :=
  ∀ r₁ r₂ r₃ n₁ n₂ : ℕ, r₃ ≤ r₂ → r₂ ≤ r₁ → n₂ ≤ r₂ → n₁ ≤ r₃ →
    eightFlagSlice (r₁ + 2) r₂ r₃ n₁ n₂ =
      X ^ (3 + 3 * r₁) * eightFlagSlice r₁ r₂ r₃ n₁ n₂ +
        X ^ (2 + 2 * (r₁ - r₂)) *
          (eightFlagSlice (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ +
            X ^ (r₂ - n₂) * eightFlagSlice (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1))

/-- `KernEightN1` implies `KernEightPrime`. -/
theorem kernEightPrime_of_kernN1 (h : KernEightN1) : KernEightPrime := by
  intro r₁ r₂ r₃ n₂ h₃₂ h₂₁ hn₂
  simp only [eightSlice_eq_sum_flagSlice, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n₁ hn₁ ↦ ?_
  simp only [Finset.mem_range] at hn₁
  rw [h r₁ r₂ r₃ n₁ n₂ h₃₂ h₂₁ hn₂ (by omega)]
  ring

/-- `KernEightN1` implies `RecEightLHS`. -/
theorem recEightLHS_of_kernN1 (h : KernEightN1) : RecEightLHS :=
  recEightLHS_of_kern (kernEightPrime_of_kernN1 h)

end HJOA3.SumToSum.ThreeTwo
