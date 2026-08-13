module

public import HJOA3.SumToSum.ThreeTwo.EightResidual
public import HJOA3.QChooseTilt
public import HJOA3.QChooseSqSum
import Mathlib.Tactic.LinearCombination

/-!
# `ResidualEight`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

private theorem sqN_succ_succ (a m : ℕ) :
    (a + 1) ^ 2 + (m + 1) ^ 2 - (a + 1) * (m + 1) = a ^ 2 + m ^ 2 - a * m + a + m + 1 := by
  have h := sqExp_toNat_succ_succ a m
  rw [sqExp_toNat, sqExp_toNat] at h
  omega

private theorem sqN_succ_left (a m : ℕ) :
    (a + 1) ^ 2 + m ^ 2 - (a + 1) * m + m = a ^ 2 + m ^ 2 - a * m + (2 * a + 1) := by
  have h := sqExp_toNat_succ_left a m
  rw [sqExp_toNat, sqExp_toNat] at h
  omega

private theorem sqN_succ_right (a m : ℕ) :
    a + (a ^ 2 + (m + 1) ^ 2 - a * (m + 1)) = a ^ 2 + m ^ 2 - a * m + (2 * m + 1) := by
  rw [← sqExp_toNat a (m + 1), ← sqExp_toNat a m]
  have h₁ := sqExp_nonneg a (m + 1)
  have h₀ := sqExp_nonneg a m
  have key : sqExp a (m + 1) + a = sqExp a m + 2 * m + 1 := by
    simp only [sqExp]; push_cast; ring
  omega

/--
Terms of a sum against `qbinom{L}{k}` past `k = L` vanish, so an over-wide binder can be
trimmed to the tight one.
-/
private theorem sum_qChoose_pad {R : Type*} [CommSemiring R] (q : R) (f : ℕ → R) (L M : ℕ)
    (h : L + 1 ≤ M) :
    ∑ k ∈ range M, f k * qChoose q L k = ∑ k ∈ range (L + 1), f k * qChoose q L k :=
  (Finset.sum_subset (Finset.range_subset_range.mpr h) fun k _ hk ↦ by
    rw [qChoose_eq_zero_of_lt (q := q) (by simpa using hk : L < k), mul_zero]).symm

/-- The inner `m₁`-sum of all three double sums, at tilt `t`. -/
private noncomputable def blk (a t L : ℕ) : ℤ[X] :=
  ∑ k ∈ range (L + 1), X ^ (a ^ 2 + k ^ 2 - a * k + t * k) * qChoose X L k

private theorem blk_zero (a t : ℕ) : blk a t 0 = X ^ a ^ 2 := by simp [blk]

/--
Reindexing the tilt: `X ^ k` times the tilt-`t` weight is the tilt-`(t+1)` weight, so a tilted
sum against `qbinom{m}{k}` over any wide enough binder is the next block up.
-/
private theorem blk_tilt_step (a t m M : ℕ) (h : m + 1 ≤ M) :
    ∑ k ∈ range M, (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + t * k) * (X ^ k * qChoose X m k) =
      blk a (t + 1) m := by
  have hterm : ∀ k ∈ range M,
      (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + t * k) * (X ^ k * qChoose X m k) =
        X ^ (a ^ 2 + k ^ 2 - a * k + (t + 1) * k) * qChoose X m k := by
    intro k _
    have he : a ^ 2 + k ^ 2 - a * k + t * k + k = a ^ 2 + k ^ 2 - a * k + (t + 1) * k := by ring
    have hx : (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + t * k + k) =
        X ^ (a ^ 2 + k ^ 2 - a * k + (t + 1) * k) := by rw [he]
    linear_combination qChoose X m k * hx
  rw [Finset.sum_congr rfl hterm,
    sum_qChoose_pad (X : ℤ[X]) (fun k ↦ X ^ (a ^ 2 + k ^ 2 - a * k + (t + 1) * k)) m M h, blk]

/-- `q`-Pascal on the untilted block. -/
private theorem blk_pascal_zero (a m : ℕ) :
    X ^ a * blk a 0 (m + 1) = X ^ a * blk a 1 m + X * blk a 2 m := by
  have hsplit := sum_qChoose_succ_split (X : ℤ[X]) (fun k ↦ X ^ (a ^ 2 + k ^ 2 - a * k + 0 * k)) m
  have e0 : blk a 0 (m + 1) =
      ∑ k ∈ range (m + 2), (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + 0 * k) *
        qChoose X (m + 1) k := by rw [blk]
  have e1 : (X : ℤ[X]) ^ a * ∑ k ∈ range (m + 1),
      X ^ (a ^ 2 + (k + 1) ^ 2 - a * (k + 1) + 0 * (k + 1)) * qChoose X m k = X * blk a 2 m := by
    rw [blk, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have he : a + (a ^ 2 + (k + 1) ^ 2 - a * (k + 1) + 0 * (k + 1)) =
        1 + (a ^ 2 + k ^ 2 - a * k + 2 * k) := by
      have := sqN_succ_right a k
      omega
    have hx : (X : ℤ[X]) ^ (a + (a ^ 2 + (k + 1) ^ 2 - a * (k + 1) + 0 * (k + 1))) =
        X ^ (1 + (a ^ 2 + k ^ 2 - a * k + 2 * k)) := by rw [he]
    linear_combination qChoose X m k * hx
  have e2 : ∑ k ∈ range (m + 2), (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + 0 * k) *
      (X ^ k * qChoose X m k) = blk a 1 m := blk_tilt_step a 0 m (m + 2) (by omega)
  rw [e0, hsplit, mul_add, e1, e2]
  ring

/-- `q`-Pascal on the tilt-`1` block, the other form. -/
private theorem blk_pascal_one (a m : ℕ) :
    X ^ a * blk a 1 (m + 1) = X ^ a * blk a 1 m + X ^ (m + 2) * blk a 2 m := by
  have hsplit := sum_qChoose_succ_split' (X : ℤ[X]) (fun k ↦ X ^ (a ^ 2 + k ^ 2 - a * k + 1 * k)) m
  have e0 : blk a 1 (m + 1) =
      ∑ k ∈ range (m + 2), (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + 1 * k) *
        qChoose X (m + 1) k := by rw [blk]
  have e1 : (X : ℤ[X]) ^ a * ∑ k ∈ range (m + 1),
      X ^ (a ^ 2 + (k + 1) ^ 2 - a * (k + 1) + 1 * (k + 1)) * (X ^ (m - k) * qChoose X m k) =
        X ^ (m + 2) * blk a 2 m := by
    rw [blk, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkm : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
    have he : a + (a ^ 2 + (k + 1) ^ 2 - a * (k + 1) + 1 * (k + 1)) + (m - k) =
        m + 2 + (a ^ 2 + k ^ 2 - a * k + 2 * k) := by
      have := sqN_succ_right a k
      omega
    have hx : (X : ℤ[X]) ^ (a + (a ^ 2 + (k + 1) ^ 2 - a * (k + 1) + 1 * (k + 1)) + (m - k)) =
        X ^ (m + 2 + (a ^ 2 + k ^ 2 - a * k + 2 * k)) := by rw [he]
    linear_combination qChoose X m k * hx
  have e2 : ∑ k ∈ range (m + 2), (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + 1 * k) *
      qChoose X m k = blk a 1 m :=
    sum_qChoose_pad (X : ℤ[X]) (fun k ↦ X ^ (a ^ 2 + k ^ 2 - a * k + 1 * k)) m (m + 2) (by omega)
  rw [e0, hsplit, mul_add, e1, e2]
  ring

/-- One tilt on the block, i.e. -/
private theorem blk_tilt (a m : ℕ) :
    blk a 2 (m + 1) = X ^ (m + 1) * blk a 1 (m + 1) + (1 - X ^ (m + 1)) * blk a 2 m := by
  have h := sum_pow_mul_qChoose_succ (X : ℤ[X])
    (fun k ↦ X ^ (a ^ 2 + k ^ 2 - a * k + 1 * k)) m
  have e1 : ∑ k ∈ range (m + 2), (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + 1 * k) *
      (X ^ k * qChoose X (m + 1) k) = blk a 2 (m + 1) :=
    blk_tilt_step a 1 (m + 1) (m + 2) (by omega)
  have e2 : ∑ k ∈ range (m + 2), (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + 1 * k) *
      qChoose X (m + 1) k = blk a 1 (m + 1) := by rw [blk]
  have e3 : ∑ k ∈ range (m + 2), (X : ℤ[X]) ^ (a ^ 2 + k ^ 2 - a * k + 1 * k) *
      (X ^ k * qChoose X m k) = blk a 2 m := blk_tilt_step a 1 m (m + 2) (by omega)
  rw [← e1, ← e2, ← e3]
  exact h

/-- The tilt-`2`-free combination. -/
private theorem blk_C (a m : ℕ) :
    X ^ (a + m + 1) * blk a 0 (m + 1 + 1) =
      X ^ (2 * m + 3) * blk a 1 (m + 1) + X ^ a * blk a 1 (m + 1) +
        (X ^ (a + m + 1) - X ^ a) * blk a 1 m := by
  have hII := blk_pascal_zero a (m + 1)
  have hI := blk_tilt a m
  have hIV := blk_pascal_one a m
  linear_combination X ^ (m + 1) * hII + X ^ (m + 2) * hI + (X ^ (m + 1) - 1) * hIV

/-- The `m₂`-th summand of `eightRem - eightPartB`, with the `X ^ r₃²` prefactor stripped. -/
private noncomputable def bigT (a m : ℕ) : ℤ[X] :=
  X ^ ((a + 1) ^ 2 + (m + 1) ^ 2 - (a + 1) * (m + 1)) * blk a 0 (m + 1) -
    X ^ (a ^ 2 + m ^ 2 - a * m + (a + 1)) * blk a 1 m

/-- The `m₂`-th summand of `eightD₂`, with the `X ^ (r₃² + r₃ + 1)` prefactor stripped. -/
private noncomputable def bigU (a m : ℕ) : ℤ[X] :=
  X ^ ((a + 1) ^ 2 + (m + 1) ^ 2 - (a + 1) * (m + 1)) * blk a 1 m

private theorem bigB_zero (a : ℕ) : X ^ a * bigT a 0 = X ^ (0 + 1) * bigU a 0 := by
  have hII := blk_pascal_zero a 0
  rw [blk_zero a 1, blk_zero a 2] at hII
  have hE : (a + 1) ^ 2 + (0 + 1) ^ 2 - (a + 1) * (0 + 1) = a ^ 2 + 0 ^ 2 - a * 0 + (a + 1) := by
    have := sqN_succ_succ a 0
    omega
  rw [bigT, bigU, blk_zero a 1, hE]
  linear_combination X ^ (a ^ 2 + 0 ^ 2 - a * 0 + (a + 1)) * hII

private theorem bigB_succ (a m : ℕ) :
    X ^ a * bigT a (m + 1) =
      X ^ (m + 2) * bigU a (m + 1) - X ^ (m + 1) * (1 - X ^ (m + 1)) * bigU a m := by
  have h1 : (X : ℤ[X]) ^ ((a + 1) ^ 2 + (m + 1 + 1) ^ 2 - (a + 1) * (m + 1 + 1)) =
      X ^ (a ^ 2 + (m + 1) ^ 2 - a * (m + 1)) * X ^ a * X ^ (m + 1) * X := by
    rw [sqN_succ_succ a (m + 1)]
    ring
  have h2 : (X : ℤ[X]) ^ ((a + 1) ^ 2 + (m + 1) ^ 2 - (a + 1) * (m + 1)) * X ^ (m + 1) =
      X ^ (a ^ 2 + (m + 1) ^ 2 - a * (m + 1)) * X ^ a * X ^ a * X := by
    rw [← pow_add, sqN_succ_left a (m + 1)]
    ring
  rw [bigT, bigU, bigU]
  linear_combination (X ^ a * blk a 0 (m + 1 + 1) - X ^ (m + 2) * blk a 1 (m + 1)) * h1 +
    blk a 1 m * (1 - X ^ (m + 1)) * h2 +
    X ^ (a ^ 2 + (m + 1) ^ 2 - a * (m + 1)) * X ^ (a + 1) * blk_C a m

/-- The uniform relation. -/
private theorem bigB (a m : ℕ) :
    X ^ a * bigT a m =
      X ^ (m + 1) * bigU a m - X ^ m * (1 - X ^ m) * bigU a (m - 1) := by
  match m with
  | 0 => simpa using bigB_zero a
  | m + 1 => simpa using bigB_succ a m

/-- The partial sums of `ResidualEight`'s summand. -/
private noncomputable def bigA (a n m : ℕ) : ℤ[X] :=
  qChoose X n m * (1 - X ^ m) * X ^ m * bigU a (m - 1)

/-- `bigA` telescopes the summand. -/
private theorem bigA_sub (a n m : ℕ) :
    qChoose X n m * (X ^ a * bigT a m - X ^ (n + 1) * bigU a m) =
      bigA a n (m + 1) - bigA a n m := by
  rcases le_or_gt m n with hmn | hmn
  · have hB := bigB a m
    have habs := qChoose_one_sub_pow_mul (X : ℤ[X]) n m
    have hpow : (X : ℤ[X]) ^ (m + 1) * X ^ (n - m) = X ^ (n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [bigA, Nat.add_sub_cancel]
    linear_combination qChoose X n m * hB + X ^ (m + 1) * bigU a m * habs +
      qChoose X n m * bigU a m * hpow
  · simp only [bigA, qChoose_eq_zero_of_lt (q := (X : ℤ[X])) hmn,
      qChoose_eq_zero_of_lt (q := (X : ℤ[X])) (by omega : n < m + 1)]
    ring

/--
The telescoped sum over the full outer range vanishes: the boundary term at `m = 2a + 2`
carries `qbinom{n}{2a+2} = 0` because `n ≤ 2a`, and the one at `m = 0` carries `1 - X ^ 0 = 0`.
-/
private theorem sum_telescope (a n : ℕ) (hn : n ≤ 2 * a) :
    ∑ m ∈ range (2 * a + 2), qChoose (X : ℤ[X]) n m *
      (X ^ a * bigT a m - X ^ (n + 1) * bigU a m) = 0 := by
  rw [Finset.sum_congr rfl (fun m _ ↦ bigA_sub a n m), Finset.sum_range_sub (bigA a n), bigA, bigA,
    qChoose_eq_zero_of_lt (q := (X : ℤ[X])) (by omega : n < 2 * a + 2)]
  simp

private theorem inner_block (a t L M : ℕ) (A : ℤ[X]) (pre : ℕ) (hLM : L + 1 ≤ M) (E : ℕ → ℕ)
    (hE : ∀ m₁, E m₁ = pre + (a ^ 2 + m₁ ^ 2 - a * m₁ + t * m₁)) :
    ∑ m₁ ∈ range M, X ^ E m₁ * A * qChoose X L m₁ = A * (X ^ pre * blk a t L) := by
  rw [sum_qChoose_pad (X : ℤ[X]) (fun m₁ ↦ X ^ E m₁ * A) L M hLM, blk, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
  rw [hE m₁]
  ring

private theorem eightRem_eq (a r₃ : ℕ) :
    eightRem a r₃ = ∑ m₂ ∈ range (2 * a + 2), qChoose X (a + r₃) m₂ *
      (X ^ (r₃ ^ 2 + ((a + 1) ^ 2 + (m₂ + 1) ^ 2 - (a + 1) * (m₂ + 1))) * blk a 0 (m₂ + 1)) := by
  rw [eightRem, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₂ hm₂ ↦ ?_
  have hm : m₂ < 2 * a + 2 := by simpa using hm₂
  exact inner_block a 0 (m₂ + 1) (2 * a + 3) (qChoose X (a + r₃) m₂)
    (r₃ ^ 2 + ((a + 1) ^ 2 + (m₂ + 1) ^ 2 - (a + 1) * (m₂ + 1))) (by omega)
    (fun m₁ ↦ r₃ ^ 2 + ((a ^ 2 + m₁ ^ 2 - a * m₁) +
      ((a + 1) ^ 2 + (m₂ + 1) ^ 2 - (a + 1) * (m₂ + 1)))) (fun m₁ ↦ by omega)

private theorem eightD₂_eq (a r₃ : ℕ) (h : r₃ ≤ a) :
    eightD₂ a r₃ = ∑ m₂ ∈ range (2 * a + 2), qChoose X (a + r₃) m₂ *
      (X ^ (r₃ ^ 2 + r₃ + 1 + ((a + 1) ^ 2 + (m₂ + 1) ^ 2 - (a + 1) * (m₂ + 1))) *
        blk a 1 m₂) := by
  rw [eightD₂, Finset.sum_comm, Finset.sum_range_succ,
    qChoose_eq_zero_of_lt (q := (X : ℤ[X])) (by omega : a + r₃ < 2 * a + 2)]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun m₂ hm₂ ↦ ?_
  have hm : m₂ < 2 * a + 2 := by simpa using hm₂
  exact inner_block a 1 m₂ (2 * a + 3) (qChoose X (a + r₃) m₂)
    (r₃ ^ 2 + r₃ + 1 + ((a + 1) ^ 2 + (m₂ + 1) ^ 2 - (a + 1) * (m₂ + 1))) (by omega)
    (fun m₁ ↦ r₃ ^ 2 + r₃ + 1 + ((a ^ 2 + m₁ ^ 2 - a * m₁) + m₁) +
      ((a + 1) ^ 2 + (m₂ + 1) ^ 2 - (a + 1) * (m₂ + 1))) (fun m₁ ↦ by omega)

private theorem eightPartB_eq (a r₃ : ℕ) (h : r₃ ≤ a) :
    eightPartB a r₃ = ∑ m₂ ∈ range (2 * a + 2), qChoose X (a + r₃) m₂ *
      (X ^ (r₃ ^ 2 + (a ^ 2 + m₂ ^ 2 - a * m₂) + (a + 1)) * blk a 1 m₂) := by
  rw [eightPartB, Finset.sum_range_succ,
    qChoose_eq_zero_of_lt (q := (X : ℤ[X])) (by omega : a + r₃ < 2 * a + 2)]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun m₂ hm₂ ↦ ?_
  have hm : m₂ < 2 * a + 2 := by simpa using hm₂
  exact inner_block a 1 m₂ (2 * a + 2) (qChoose X (a + r₃) m₂)
    (r₃ ^ 2 + (a ^ 2 + m₂ ^ 2 - a * m₂) + (a + 1)) (by omega)
    (fun m₁ ↦ r₃ ^ 2 + (a ^ 2 + m₂ ^ 2 - a * m₂) + (a + 1) + (a ^ 2 + m₁ ^ 2 - a * m₁ + m₁))
    (fun m₁ ↦ by omega)

private theorem residual_eq (a r₃ : ℕ) (h : r₃ ≤ a) :
    eightRem a r₃ - eightD₂ a r₃ - eightPartB a r₃ =
      X ^ r₃ ^ 2 * ∑ m₂ ∈ range (2 * a + 2),
        qChoose X (a + r₃) m₂ * (bigT a m₂ - X ^ (r₃ + 1) * bigU a m₂) := by
  rw [eightRem_eq, eightD₂_eq a r₃ h, eightPartB_eq a r₃ h, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m₂ _ ↦ ?_
  rw [bigT, bigU]
  ring

/-- `ResidualEight`. -/
theorem residualEight : ResidualEight := fun a r₃ h ↦ by
  have hne : (X : ℤ[X]) ^ a ≠ 0 := pow_ne_zero a X_ne_zero
  have hsum := sum_telescope a (a + r₃) (by omega)
  have key : (X : ℤ[X]) ^ a * (eightRem a r₃ - eightD₂ a r₃ - eightPartB a r₃) = 0 := by
    rw [residual_eq a r₃ h, ← mul_assoc, mul_comm ((X : ℤ[X]) ^ a) (X ^ r₃ ^ 2), mul_assoc,
      Finset.mul_sum]
    have hterm : ∀ m ∈ range (2 * a + 2), (X : ℤ[X]) ^ a *
        (qChoose X (a + r₃) m * (bigT a m - X ^ (r₃ + 1) * bigU a m)) =
        qChoose X (a + r₃) m * (X ^ a * bigT a m - X ^ (a + r₃ + 1) * bigU a m) := by
      intro m _
      ring
    rw [Finset.sum_congr rfl hterm, hsum, mul_zero]
  have hD := (mul_eq_zero.mp key).resolve_left hne
  linear_combination hD

/-- `BaseEight`, the `b = 8` base case, now unconditionally. -/
theorem baseEight : BaseEight := baseEight_of_residual residualEight

end HJOA3.SumToSum.ThreeTwo
