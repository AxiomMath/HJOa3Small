module

public import QSeriesLib.NumberTheory.QTheory.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Tilting a `q`-binomial sum, and the absorption relation
-/

@[expose] public section

open Finset

namespace HJOA3

variable {R : Type*} [CommRing R] (q : R)

/-- The absorption relation. -/
theorem qChoose_one_sub_pow_mul (n k : ℕ) :
    (1 - q ^ (n - k)) * qChoose q n k = (1 - q ^ (k + 1)) * qChoose q n (k + 1) := by
  have h : qChoose q n k + q ^ (k + 1) * qChoose q n (k + 1) =
      q ^ (n - k) * qChoose q n k + qChoose q n (k + 1) :=
    (qChoose_succ_succ (q := q)).symm.trans (qChoose_succ_succ' (q := q))
  linear_combination h

/-- One tilt, termwise. -/
theorem qChooseTilt_pow_mul (m k : ℕ) :
    q ^ k * qChoose q (m + 1) k =
      q ^ (m + 1) * qChoose q (m + 1) k + (1 - q ^ (m + 1)) * (q ^ k * qChoose q m k) := by
  match k with
  | 0 => simp
  | j + 1 =>
    rcases le_or_gt j m with hj | hj
    · have hpow : q ^ (j + 1) * q ^ (m - j) = q ^ (m + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have h₁ : qChoose q (m + 1) (j + 1) =
          qChoose q m j + q ^ (j + 1) * qChoose q m (j + 1) := qChoose_succ_succ
      have h₂ : qChoose q (m + 1) (j + 1) =
          q ^ (m - j) * qChoose q m j + qChoose q m (j + 1) := qChoose_succ_succ'
      linear_combination (qChoose q (m + 1) (j + 1) - q ^ (j + 1) * qChoose q m (j + 1)) * hpow -
        q ^ (j + 1) * q ^ (m - j) * h₁ + q ^ (j + 1) * h₂
    · rw [qChoose_eq_zero_of_lt (q := q) (by omega : m < j + 1),
        qChoose_eq_zero_of_lt (q := q) (by omega : m + 1 < j + 1)]
      ring

/-- `q`-Pascal against any coefficients. -/
theorem sum_qChoose_succ_split (c : ℕ → R) (m : ℕ) :
    ∑ k ∈ range (m + 2), c k * qChoose q (m + 1) k =
      ∑ k ∈ range (m + 1), c (k + 1) * qChoose q m k +
        ∑ k ∈ range (m + 2), c k * (q ^ k * qChoose q m k) := by
  have hS : ∑ j ∈ range (m + 1), c (j + 1) * qChoose q (m + 1) (j + 1) =
      ∑ j ∈ range (m + 1), c (j + 1) * qChoose q m j +
        ∑ j ∈ range (m + 1), c (j + 1) * (q ^ (j + 1) * qChoose q m (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by
      linear_combination c (j + 1) * qChoose_succ_succ (q := q) (n := m) (k := j)
  rw [Finset.sum_range_succ' (fun k ↦ c k * qChoose q (m + 1) k) (m + 1),
    Finset.sum_range_succ' (fun k ↦ c k * (q ^ k * qChoose q m k)) (m + 1), hS,
    qChoose_zero (q := q) (n := m + 1), qChoose_zero (q := q) (n := m)]
  ring

/-- `q`-Pascal against any coefficients, the other form. -/
theorem sum_qChoose_succ_split' (c : ℕ → R) (m : ℕ) :
    ∑ k ∈ range (m + 2), c k * qChoose q (m + 1) k =
      ∑ k ∈ range (m + 1), c (k + 1) * (q ^ (m - k) * qChoose q m k) +
        ∑ k ∈ range (m + 2), c k * qChoose q m k := by
  have hS : ∑ j ∈ range (m + 1), c (j + 1) * qChoose q (m + 1) (j + 1) =
      ∑ j ∈ range (m + 1), c (j + 1) * (q ^ (m - j) * qChoose q m j) +
        ∑ j ∈ range (m + 1), c (j + 1) * qChoose q m (j + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by
      linear_combination c (j + 1) * qChoose_succ_succ' (q := q) (n := m) (k := j)
  rw [Finset.sum_range_succ' (fun k ↦ c k * qChoose q (m + 1) k) (m + 1),
    Finset.sum_range_succ' (fun k ↦ c k * qChoose q m k) (m + 1), hS,
    qChoose_zero (q := q) (n := m + 1), qChoose_zero (q := q) (n := m)]
  ring

/-- One tilt, against any coefficients. -/
theorem sum_pow_mul_qChoose_succ (c : ℕ → R) (m : ℕ) :
    ∑ k ∈ range (m + 2), c k * (q ^ k * qChoose q (m + 1) k) =
      q ^ (m + 1) * ∑ k ∈ range (m + 2), c k * qChoose q (m + 1) k +
        (1 - q ^ (m + 1)) * ∑ k ∈ range (m + 2), c k * (q ^ k * qChoose q m k) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  linear_combination c k * qChooseTilt_pow_mul q m k

end HJOA3
