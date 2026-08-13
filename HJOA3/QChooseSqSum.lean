module

public import QSeriesLib.NumberTheory.QTheory.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# `q`-binomial sums against a completed-square weight
-/

@[expose] public section

open Finset

namespace HJOA3

variable {R : Type*} [CommSemiring R] (q : R)

/--
The weight exponent of `qChooseSqSum`: the quadratic form `a² + m² - a m`, which is `m² - a m`
shifted by the constant that makes it nonnegative.
-/
def sqExp (a m : ℕ) : ℤ := a ^ 2 + m ^ 2 - a * m

/-- `sqExp` is nonnegative everywhere — no hypotheses at all. -/
theorem sqExp_nonneg (a m : ℕ) : 0 ≤ sqExp a m := by
  simp only [sqExp]
  nlinarith [sq_nonneg ((a : ℤ) - m), sq_nonneg (a : ℤ), sq_nonneg (m : ℤ)]

/-- The `(a, m) ↦ (a + 1, m + 1)` weight shift. -/
theorem sqExp_toNat_succ_succ (a m : ℕ) :
    (sqExp (a + 1) (m + 1)).toNat = (sqExp a m).toNat + a + m + 1 := by
  have h₁ := sqExp_nonneg (a + 1) (m + 1)
  have h₀ := sqExp_nonneg a m
  have key : sqExp (a + 1) (m + 1) = sqExp a m + a + m + 1 := by
    simp only [sqExp]; push_cast; ring
  omega

/-- The `a ↦ a + 1` weight shift at fixed `m`. -/
theorem sqExp_toNat_succ_left (a m : ℕ) :
    (sqExp (a + 1) m).toNat + m = (sqExp a m).toNat + 2 * a + 1 := by
  have h₁ := sqExp_nonneg (a + 1) m
  have h₀ := sqExp_nonneg a m
  have key : sqExp (a + 1) m + m = sqExp a m + 2 * a + 1 := by
    simp only [sqExp]; push_cast; ring
  omega

/-- The `a ↦ a + 2` weight shift at fixed `m`. -/
theorem sqExp_toNat_add_two (a m : ℕ) :
    (sqExp (a + 2) m).toNat + m = (sqExp (a + 1) m).toNat + 2 * a + 3 := by
  have h₂ := sqExp_nonneg (a + 2) m
  have h₁ := sqExp_nonneg (a + 1) m
  have key : sqExp (a + 2) m + m = sqExp (a + 1) m + 2 * a + 3 := by
    simp only [sqExp]; push_cast; ring
  omega

/-- The `(a, m) ↦ (a + 2, m + 1)` weight shift. -/
theorem sqExp_toNat_add_two_succ (a m : ℕ) :
    (sqExp (a + 2) (m + 1)).toNat = (sqExp a m).toNat + 3 * a + 3 := by
  have h₂ := sqExp_nonneg (a + 2) (m + 1)
  have h₀ := sqExp_nonneg a m
  have key : sqExp (a + 2) (m + 1) = sqExp a m + 3 * a + 3 := by
    simp only [sqExp]; push_cast; ring
  omega

/-- `sqExp` in `ℕ`-subtraction form. -/
theorem sqExp_toNat (a m : ℕ) : (sqExp a m).toNat = a ^ 2 + m ^ 2 - a * m := by
  have h := sqExp_nonneg a m
  have key : sqExp a m + ((a * m : ℕ) : ℤ) = ((a ^ 2 + m ^ 2 : ℕ) : ℤ) := by
    simp only [sqExp]; push_cast; ring
  omega

/--
`∑ m ≤ N, q ^ (a² + m² - a m) * qbinom{N}{m}` — the block both sides of the `b = 8` identity
are built from.
-/
def qChooseSqSum (N a : ℕ) : R :=
  ∑ m ∈ range (N + 1), q ^ (sqExp a m).toNat * qChoose q N m

/-- The binder may be widened at will. -/
theorem qChooseSqSum_eq_sum_range {N M : ℕ} (hM : N ≤ M) (a : ℕ) :
    qChooseSqSum q N a = ∑ m ∈ range (M + 1), q ^ (sqExp a m).toNat * qChoose q N m := by
  rw [qChooseSqSum]
  refine Finset.sum_subset (by simpa using Nat.succ_le_succ hM) fun m _ hm ↦ ?_
  simp only [mem_range, not_lt] at hm
  rw [qChoose_eq_zero_of_lt hm, mul_zero]

/-- The `m = N + 1` term vanishes, so the defining sum may be taken over `range (N + 2)`. -/
theorem qChooseSqSum_eq_sum_range_add_two (N a : ℕ) :
    qChooseSqSum q N a = ∑ m ∈ range (N + 2), q ^ (sqExp a m).toNat * qChoose q N m := by
  rw [Finset.sum_range_succ, qChoose_eq_zero_of_lt (Nat.lt_succ_self N), mul_zero, add_zero,
    qChooseSqSum]

/-- First contiguous relation: moving `(N, a)` up by `(1, 1)`. -/
theorem qChooseSqSum_succ_succ (N a : ℕ) :
    qChooseSqSum q (N + 1) (a + 1) =
      qChooseSqSum q N (a + 1) + q ^ (N + a + 1) * qChooseSqSum q N a := by
  have hlhs : qChooseSqSum q (N + 1) (a + 1) =
      (∑ m ∈ range (N + 1), q ^ (sqExp (a + 1) (m + 1)).toNat * qChoose q (N + 1) (m + 1)) +
        q ^ (sqExp (a + 1) 0).toNat * qChoose q (N + 1) 0 :=
    Finset.sum_range_succ' _ (N + 1)
  have hrhs : qChooseSqSum q N (a + 1) =
      (∑ m ∈ range (N + 1), q ^ (sqExp (a + 1) (m + 1)).toNat * qChoose q N (m + 1)) +
        q ^ (sqExp (a + 1) 0).toNat * qChoose q N 0 := by
    rw [qChooseSqSum_eq_sum_range_add_two q N (a + 1)]
    exact Finset.sum_range_succ' _ (N + 1)
  have hmul : (∑ m ∈ range (N + 1), q ^ (N + a + 1) * (q ^ (sqExp a m).toNat * qChoose q N m)) =
      q ^ (N + a + 1) * qChooseSqSum q N a := (Finset.mul_sum _ _ _).symm
  have key : (∑ m ∈ range (N + 1),
        q ^ (sqExp (a + 1) (m + 1)).toNat * qChoose q (N + 1) (m + 1)) =
      (∑ m ∈ range (N + 1), q ^ (sqExp (a + 1) (m + 1)).toNat * qChoose q N (m + 1)) +
        ∑ m ∈ range (N + 1), q ^ (N + a + 1) * (q ^ (sqExp a m).toNat * qChoose q N m) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    simp only [mem_range] at hm
    have he : (sqExp (a + 1) (m + 1)).toNat + (N - m) = N + a + 1 + (sqExp a m).toNat := by
      have := sqExp_toNat_succ_succ a m
      omega
    rw [qChoose_succ_succ', mul_add, ← mul_assoc, ← pow_add, he, pow_add, mul_assoc]
    ring
  rw [hlhs, hrhs, key, hmul, qChoose_zero, qChoose_zero]
  ring

/-- Second contiguous relation: moving `(N, a)` up by `(1, 2)`. -/
theorem qChooseSqSum_succ_add_two (N a : ℕ) :
    qChooseSqSum q (N + 1) (a + 2) =
      q ^ (2 * a + 3) * qChooseSqSum q N (a + 1) + q ^ (3 * a + 3) * qChooseSqSum q N a := by
  have hlhs : qChooseSqSum q (N + 1) (a + 2) =
      (∑ m ∈ range (N + 1), q ^ (sqExp (a + 2) (m + 1)).toNat * qChoose q (N + 1) (m + 1)) +
        q ^ (sqExp (a + 2) 0).toNat * qChoose q (N + 1) 0 :=
    Finset.sum_range_succ' _ (N + 1)
  have hfirst : (∑ m ∈ range (N + 1), q ^ (sqExp (a + 2) (m + 1)).toNat * qChoose q N m) =
      q ^ (3 * a + 3) * qChooseSqSum q N a := by
    rw [qChooseSqSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [← mul_assoc, ← pow_add, sqExp_toNat_add_two_succ a m]
    ring
  have hblock : (∑ m ∈ range (N + 1),
        q ^ ((sqExp (a + 2) (m + 1)).toNat + (m + 1)) * qChoose q N (m + 1)) +
      q ^ (sqExp (a + 2) 0).toNat * qChoose q (N + 1) 0 =
      q ^ (2 * a + 3) * qChooseSqSum q N (a + 1) := by
    have h0 : q ^ (sqExp (a + 2) 0).toNat * qChoose q (N + 1) 0 =
        q ^ ((sqExp (a + 2) 0).toNat + 0) * qChoose q N 0 := by simp
    rw [h0, ← Finset.sum_range_succ'
      (fun m ↦ q ^ ((sqExp (a + 2) m).toNat + m) * qChoose q N m) (N + 1),
      Finset.sum_range_succ, qChoose_eq_zero_of_lt (Nat.lt_succ_self N), mul_zero, add_zero,
      qChooseSqSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [← mul_assoc, ← pow_add, sqExp_toNat_add_two a m]
    ring
  have key : (∑ m ∈ range (N + 1),
        q ^ (sqExp (a + 2) (m + 1)).toNat * qChoose q (N + 1) (m + 1)) =
      (∑ m ∈ range (N + 1), q ^ (sqExp (a + 2) (m + 1)).toNat * qChoose q N m) +
        ∑ m ∈ range (N + 1),
          q ^ ((sqExp (a + 2) (m + 1)).toNat + (m + 1)) * qChoose q N (m + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [qChoose_succ_succ, mul_add, pow_add]
    ring
  rw [hlhs, key, hfirst, add_assoc, hblock]
  ring

/-- The fixed-level contiguous relation. -/
theorem qChooseSqSum_dagger (N a : ℕ) :
    qChooseSqSum q N (a + 2) + q ^ (N + a + 2) * qChooseSqSum q N (a + 1) =
      q ^ (2 * a + 3) * qChooseSqSum q N (a + 1) + q ^ (3 * a + 3) * qChooseSqSum q N a := by
  have h := qChooseSqSum_succ_succ q N (a + 1)
  rw [show N + (a + 1) + 1 = N + a + 2 from by omega] at h
  rw [← h, qChooseSqSum_succ_add_two]

/-- The two-step relation `(N, a) ↦ (N + 2, a + 2)`. -/
theorem qChooseSqSum_add_two_add_two (N a : ℕ) :
    qChooseSqSum q (N + 2) (a + 2) =
      (q ^ (2 * a + 3) + q ^ (N + a + 3)) * qChooseSqSum q N (a + 1) +
        (q ^ (3 * a + 3) + q ^ (2 * N + 2 * a + 4)) * qChooseSqSum q N a := by
  have hstep : qChooseSqSum q (N + 2) (a + 2) =
      qChooseSqSum q (N + 1) (a + 2) + q ^ (N + a + 3) * qChooseSqSum q (N + 1) (a + 1) := by
    have h := qChooseSqSum_succ_succ q (N + 1) (a + 1)
    rw [show N + 1 + (a + 1) + 1 = N + a + 3 from by omega] at h
    exact h
  have hp : q ^ (2 * N + 2 * a + 4) = q ^ (N + a + 3) * q ^ (N + a + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hstep, qChooseSqSum_succ_add_two q N a, qChooseSqSum_succ_succ q N a, hp]
  ring

/-- Every coefficient is a single monomial. -/
theorem qChooseSqSum_kernel (N a : ℕ) :
    qChooseSqSum q (N + 2) (a + 2) =
      q ^ (3 * a + 3) * qChooseSqSum q N a + q ^ (2 * a + 3) * qChooseSqSum q N (a + 1) +
        q ^ (N + a + 3) * qChooseSqSum q (N + 1) (a + 1) := by
  have hp : q ^ (2 * N + 2 * a + 4) = q ^ (N + a + 3) * q ^ (N + a + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [qChooseSqSum_add_two_add_two, qChooseSqSum_succ_succ q N a, hp]
  ring

end HJOA3
