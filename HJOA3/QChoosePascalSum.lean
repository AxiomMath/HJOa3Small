module

public import QSeriesLib.NumberTheory.QTheory.Basic
import Mathlib.Tactic.Ring

/-!
# One `q`-Pascal step under a summation sign
-/

@[expose] public section

open Finset

namespace HJOA3

variable {R : Type*} [CommSemiring R] (q : R)

/-- A `q`-Pascal step under a sum, in the `q ^ k` form. -/
theorem sum_qChoose_succ_mul (L : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (L + 1 + 1), qChoose q (L + 1) k * f k =
      ∑ k ∈ range (L + 1), qChoose q L k * (q ^ k * f k + f (k + 1)) := by
  rw [Finset.sum_range_succ' (fun k ↦ qChoose q (L + 1) k * f k) (L + 1), qChoose_zero, one_mul]
  have hstep : ∀ k ∈ range (L + 1), qChoose q (L + 1) (k + 1) * f (k + 1) =
      qChoose q L k * f (k + 1) + qChoose q L (k + 1) * (q ^ (k + 1) * f (k + 1)) := by
    intro k _
    rw [qChoose_succ_succ]
    ring
  have hdrop : ∑ k ∈ range (L + 1), qChoose q L (k + 1) * (q ^ (k + 1) * f (k + 1)) =
      ∑ k ∈ range L, qChoose q L (k + 1) * (q ^ (k + 1) * f (k + 1)) := by
    rw [Finset.sum_range_succ, qChoose_eq_zero_of_lt (Nat.lt_succ_self L), zero_mul, add_zero]
  have hre : ∑ k ∈ range (L + 1), qChoose q L k * (q ^ k * f k) =
      (∑ k ∈ range L, qChoose q L (k + 1) * (q ^ (k + 1) * f (k + 1))) + f 0 := by
    rw [Finset.sum_range_succ' (fun k ↦ qChoose q L k * (q ^ k * f k)) L, qChoose_zero, pow_zero,
      one_mul, one_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hdrop, add_assoc, ← hre,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- A `q`-Pascal step under a sum, in the `q ^ (n-k)` form. -/
theorem sum_qChoose_succ_mul' (L : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (L + 1 + 1), qChoose q (L + 1) k * f k =
      ∑ k ∈ range (L + 1), qChoose q L k * (f k + q ^ (L - k) * f (k + 1)) := by
  rw [Finset.sum_range_succ' (fun k ↦ qChoose q (L + 1) k * f k) (L + 1), qChoose_zero, one_mul]
  have hstep : ∀ k ∈ range (L + 1), qChoose q (L + 1) (k + 1) * f (k + 1) =
      qChoose q L k * (q ^ (L - k) * f (k + 1)) + qChoose q L (k + 1) * f (k + 1) := by
    intro k _
    rw [qChoose_succ_succ']
    ring
  have hdrop : ∑ k ∈ range (L + 1), qChoose q L (k + 1) * f (k + 1) =
      ∑ k ∈ range L, qChoose q L (k + 1) * f (k + 1) := by
    rw [Finset.sum_range_succ, qChoose_eq_zero_of_lt (Nat.lt_succ_self L), zero_mul, add_zero]
  have hre : ∑ k ∈ range (L + 1), qChoose q L k * f k =
      (∑ k ∈ range L, qChoose q L (k + 1) * f (k + 1)) + f 0 := by
    rw [Finset.sum_range_succ' (fun k ↦ qChoose q L k * f k) L, qChoose_zero, one_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hdrop, add_assoc, ← hre,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The `q`-binomial row does not distinguish a sequence from its shift. -/
theorem sum_qChoose_mul_shift_comm (M : ℕ) (W : ℕ → R) :
    ∑ t ∈ range (M + 1), qChoose q M t * (W t + q ^ (M - t) * W (t + 1)) =
      ∑ t ∈ range (M + 1), qChoose q M t * (q ^ t * W t + W (t + 1)) :=
  (sum_qChoose_succ_mul' q M W).symm.trans (sum_qChoose_succ_mul q M W)

/-- The two forms of `q`-Pascal, one term at a time. -/
theorem qChoose_pascal_comm (L k : ℕ) :
    qChoose q L k + q ^ (k + 1) * qChoose q L (k + 1) =
      q ^ (L - k) * qChoose q L k + qChoose q L (k + 1) := by
  rw [← qChoose_succ_succ (q := q) (n := L) (k := k), qChoose_succ_succ']

end HJOA3
