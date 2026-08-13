module

public import QSeriesLib.NumberTheory.HJO.SumToSum.Small
public import QSeriesLib.NumberTheory.QTheory.Basic
public import QSeriesLib.NumberTheory.QTheory.Vandermonde
public import HJOA3.SumToSum.Box

/-!
# Sum-to-sum identities for `b = 4`
-/

@[expose] public section

open Finset Polynomial

namespace HJOA3.SumToSum.ThreeOne

theorem four_identity (r₁ : ℕ) :
    ∑ n₁ ∈ range (r₁ + 1), ∑ n₂ ∈ range (r₁ + 1),
      X (R := ℕ) ^ (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + n₁ * n₂ - n₁ * r₁ : ℤ).toNat *
        qChoose X r₁ n₁ * qChoose X r₁ n₂ =
    ∑ m₁ ∈ range (2 * r₁ + 1),
      X ^ (r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) * qChoose X (2 * r₁) m₁ := by
  classical
  have hexp : ∀ n₁ n₂ : ℕ, n₁ ≤ r₁ → n₂ ≤ r₁ →
      r₁ ^ 2 + (n₁ + n₂) ^ 2 - r₁ * (n₁ + n₂) + (r₁ - n₁) * n₂ =
      (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + n₁ * n₂ - n₁ * r₁ : ℤ).toNat := by
    intro n₁ n₂ h₁ h₂
    have hle : r₁ * (n₁ + n₂) ≤ r₁ ^ 2 + (n₁ + n₂) ^ 2 := by nlinarith
    have key : (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + n₁ * n₂ - n₁ * r₁ : ℤ) =
        ((r₁ ^ 2 + (n₁ + n₂) ^ 2 - r₁ * (n₁ + n₂) + (r₁ - n₁) * n₂ : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle, Nat.cast_sub h₁]
      ring
    rw [key, Int.toNat_natCast]
  have hvanish : ∀ p : ℕ × ℕ, ¬(p.1 ≤ r₁ ∧ p.2 ≤ r₁) →
      X (R := ℕ) ^ (p.1 ^ 2 + p.2 ^ 2 + r₁ ^ 2 + p.1 * p.2 - p.1 * r₁ : ℤ).toNat *
        qChoose X r₁ p.1 * qChoose X r₁ p.2 = 0 := by
    intro p hp
    rcases not_and_or.mp hp with h | h
    · rw [qChoose_eq_zero_of_lt (show r₁ < p.1 from by omega)]; ring
    · rw [qChoose_eq_zero_of_lt (show r₁ < p.2 from by omega)]; ring
  rw [Finset.sum_comm,
    sum_box_eq_sum_antidiagonal (a := r₁) (b := r₁) (N := 2 * r₁) (by omega) _ hvanish]
  refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
  rw [two_mul, qChoose_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp := (Finset.HasAntidiagonal.mem_antidiagonal
    (self := Finset.Nat.instHasAntidiagonal)).mp hp
  by_cases hb : p.1 ≤ r₁ ∧ p.2 ≤ r₁
  · subst hp
    rw [← mul_assoc, ← mul_assoc, ← pow_add, hexp p.1 p.2 hb.1 hb.2]
  · rw [hvanish p hb]
    rcases not_and_or.mp hb with h | h
    · rw [qChoose_eq_zero_of_lt (show r₁ < p.1 from by omega)]; ring
    · rw [qChoose_eq_zero_of_lt (show r₁ < p.2 from by omega)]; ring

/-- The sum-to-sum conjecture holds for `b = 4`. -/
theorem four (r₁ : ℕ) : HJO.SumToSum.ThreeOne.Conjecture 1 ![r₁] :=
  (HJO.SumToSum.ThreeOne.four_iff r₁).mpr (four_identity r₁)

end HJOA3.SumToSum.ThreeOne
