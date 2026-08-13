module

public import HJOA3.FlagStraightening
public import HJOA3.QOne
public import HJOA3.SumToSum.Box
public import HJOA3.SumToSum.ThreeTwo.Small

/-!
# The `b = 8` sum-to-sum identity at `q = 1`
-/

@[expose] public section

open Fin Finset Fintype Polynomial NumericalSemigroup NumericalSemigroup.ThreeTwo HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/-- `∑_{n₁,n₄ ≤ r} C(n₄,n₁) C(r,n₄) = 3 ^ r`: chains `X₁ ⊆ X₂ ⊆ R` with `|R| = r`. -/
theorem sum_chain_two (r : ℕ) :
    ∑ n₁ ∈ range (r + 1), ∑ n₄ ∈ range (r + 1), n₄.choose n₁ * r.choose n₄ = 3 ^ r := by
  rw [Finset.sum_comm]
  have h : ∀ n₄ ∈ range (r + 1),
      ∑ n₁ ∈ range (r + 1), n₄.choose n₁ * r.choose n₄ = r.choose n₄ * 2 ^ n₄ := by
    intro n₄ hn₄
    rw [← Finset.sum_mul, sum_range_shrink (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₄)) _
      (fun i hi ↦ Nat.choose_eq_zero_of_lt hi), Nat.sum_range_choose]
    ring
  rw [Finset.sum_congr rfl h, sum_range_choose_mul_pow r 2]

/-- The `(n₂, n₅)` half of the `b = 8` left side at `q = 1`. -/
theorem sum_ext_part (r₁ r₂ : ℕ) (h : r₂ ≤ r₁) :
    ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₁ + 1),
        r₂.choose n₂ * extChoose ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂) =
      2 ^ (r₁ - r₂) * 3 ^ r₂ := by
  have h1 : ∀ n₂ ∈ range (r₂ + 1),
      ∑ n₅ ∈ range (r₁ + 1),
        r₂.choose n₂ * extChoose ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂) =
      r₂.choose n₂ * 2 ^ (r₂ - n₂) * 2 ^ (r₁ - r₂) := by
    intro n₂ hn₂
    have hn : n₂ ≤ r₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₂)
    rw [← Finset.mul_sum, ← sum_range_shift_of_vanish (n := n₂) (N := r₁) (by omega)
      _ (fun a ha ↦ by rw [extChoose_of_neg (Or.inr (by omega))])]
    have h2 : ∀ d ∈ range (r₁ - n₂ + 1),
        extChoose ((r₁ : ℤ) - n₂) (((n₂ + d : ℕ) : ℤ) - n₂) = (r₁ - n₂).choose d := by
      intro d _
      rw [extChoose_of_nonneg (by omega) (by push_cast; omega)]
      congr 1 <;> omega
    rw [Finset.sum_congr rfl h2, Nat.sum_range_choose,
      show r₁ - n₂ = r₂ - n₂ + (r₁ - r₂) from by omega, pow_add]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, sum_range_choose_mul_pow_sub r₂ 2]
  ring

/-- The right side of the `b = 8` identity at `q = 1`. -/
theorem sum_rhs_part (r₁ r₂ r₃ : ℕ) (h₂₁ : r₂ ≤ r₁) (h₃₂ : r₃ ≤ r₂) :
    ∑ m₁ ∈ range (2 * r₁ + 1), ∑ m₂ ∈ range (2 * r₁ + 1),
        (r₁ - r₂ + m₂).choose m₁ * (r₂ + r₃).choose m₂ =
      2 ^ (r₁ - r₂) * 3 ^ (r₂ + r₃) := by
  rw [Finset.sum_comm, sum_range_shrink (show r₂ + r₃ ≤ 2 * r₁ from by omega) _
    (fun i hi ↦ Finset.sum_eq_zero fun m₁ _ ↦ by
      rw [Nat.choose_eq_zero_of_lt hi]; ring)]
  have h : ∀ m₂ ∈ range (r₂ + r₃ + 1),
      ∑ m₁ ∈ range (2 * r₁ + 1), (r₁ - r₂ + m₂).choose m₁ * (r₂ + r₃).choose m₂ =
      (r₂ + r₃).choose m₂ * 2 ^ m₂ * 2 ^ (r₁ - r₂) := by
    intro m₂ hm₂
    have hm : m₂ ≤ r₂ + r₃ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm₂)
    rw [← Finset.sum_mul, sum_range_shrink (show r₁ - r₂ + m₂ ≤ 2 * r₁ from by omega) _
      (fun i hi ↦ Nat.choose_eq_zero_of_lt hi), Nat.sum_range_choose,
      show r₁ - r₂ + m₂ = m₂ + (r₁ - r₂) from by omega, pow_add]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, sum_range_choose_mul_pow (r₂ + r₃) 2]
  ring

/-- The sum-to-sum conjecture for `b = 8` holds at `q = 1`. -/
theorem eight_at_one {r₁ r₂ r₃ : ℕ} (h₂₁ : r₂ ≤ r₁) (h₃₂ : r₃ ≤ r₂) :
    (∑ᶠ m, lhsTerm 2 ![r₁, r₂, r₃] (finspan {3, 3 * 2 + 2}).gaps m).eval 1 =
      (∑ᶠ m, rhsTerm 2 ![r₁, r₂, r₃] m).eval 1 := by
  rw [lhs_eight, rhs_eight h₂₁ h₃₂]
  simp only [eval_finsetSum, eval_mul, eval_pow, eval_X, one_pow, eval_one_qChoose,
    eval_one_extendedQChoose]
  simp only [one_mul]
  refine Eq.trans (Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_congr rfl fun n₅ _ ↦
    Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₄ _ ↦
      (?_ : _ = (r₂.choose n₂ * extChoose ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂)) *
          (n₄.choose n₁ * r₃.choose n₄))) ?_
  · ring
  rw [sum_sum_mul_sum_sum, sum_ext_part r₁ r₂ h₂₁, sum_chain_two r₃,
    sum_rhs_part r₁ r₂ r₃ h₂₁ h₃₂, pow_add]
  ring

end HJOA3.SumToSum.ThreeTwo
