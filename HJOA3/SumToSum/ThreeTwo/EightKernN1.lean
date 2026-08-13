module

public import HJOA3.QChoosePascalSum
public import HJOA3.SumToSum.ThreeTwo.EightRecLHS

/-!
# `KernEightN1`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/-- `eightN₅Sum` as an unguarded row. -/
theorem eightN₅Sum_eq_sum_range (R s r₃ n₁ n₂ n₄ : ℕ) (h : n₂ ≤ R) :
    eightN₅Sum R s r₃ n₁ n₂ n₄ =
      ∑ k ∈ range (R - n₂ + 1),
        qChoose X (R - n₂) k * X ^ (eightExp R s r₃ n₁ n₂ n₄ (n₂ + k)).toNat := by
  have hsub : Finset.Ico n₂ (R + 1) ⊆ range (R + 1) :=
    fun x hx ↦ Finset.mem_range.2 (Finset.mem_Ico.1 hx).2
  have hzero : ∀ n₅ ∈ range (R + 1), n₅ ∉ Finset.Ico n₂ (R + 1) →
      X ^ (eightExp R s r₃ n₁ n₂ n₄ n₅).toNat *
        (if n₂ ≤ n₅ then qChoose (X : ℕ[X]) (R - n₂) (n₅ - n₂) else 0) = 0 := by
    intro n₅ h₅ h₅'
    simp only [Finset.mem_range] at h₅
    simp only [Finset.mem_Ico, not_and, not_lt] at h₅'
    rw [if_neg fun hle ↦ absurd (h₅' hle) (by omega), mul_zero]
  rw [eightN₅Sum, ← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range,
    show R + 1 - n₂ = R - n₂ + 1 from by omega]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [if_pos (Nat.le_add_right n₂ k), show n₂ + k - n₂ = k from by omega]
  ring

/-- Lowering `(r₁+1, r₂+1)` to `(r₁, r₂)` and `(r₁+1, r₂+1, n₂+1)`. -/
theorem eightN₅Sum_succ_snd (r₁ r₂ r₃ n₁ n₂ t : ℕ) (h₂₁ : r₂ ≤ r₁) (hn₂ : n₂ ≤ r₂) :
    eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) =
      X ^ (t + 2 + r₁ + 2 * r₂) * eightN₅Sum r₁ r₂ r₃ n₁ n₂ (n₁ + t) +
        X ^ (t + 1 + (r₂ - n₂)) * eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) := by
  have hn₂r₁ : n₂ ≤ r₁ := hn₂.trans h₂₁
  rw [eightN₅Sum_eq_sum_range (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (by omega),
    eightN₅Sum_eq_sum_range r₁ r₂ r₃ n₁ n₂ (n₁ + t) hn₂r₁,
    eightN₅Sum_eq_sum_range (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) (by omega),
    show r₁ + 1 - n₂ = r₁ - n₂ + 1 from by omega,
    show r₁ + 1 - (n₂ + 1) = r₁ - n₂ from by omega,
    sum_qChoose_succ_mul' (X : ℕ[X]) (r₁ - n₂)
      fun k ↦ X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k)).toNat,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  have hex₁ : (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k)).toNat =
      t + 2 + r₁ + 2 * r₂ + (eightExp r₁ r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat := by
    have hZ : eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k) =
        eightExp r₁ r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k) + t + 2 + r₁ + 2 * r₂ := by
      simp only [eightExp]; push_cast; ring
    have h₀ : 0 ≤ eightExp r₁ r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k) := eightExp_nonneg
    omega
  have hex₂ : r₁ - n₂ - k +
        (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + (k + 1))).toNat =
      t + 1 + (r₂ - n₂) +
        (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) (n₂ + 1 + k)).toNat := by
    have hZ : eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + (k + 1)) + r₁ =
        eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) (n₂ + 1 + k) + t + 1 + r₂ + k := by
      simp only [eightExp]; push_cast; ring
    have h₀ : 0 ≤ eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) (n₂ + 1 + k) :=
      eightExp_nonneg
    have h₁ : 0 ≤ eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + (k + 1)) :=
      eightExp_nonneg
    omega
  have p₁ : (X : ℕ[X]) ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k)).toNat =
      X ^ (t + 2 + r₁ + 2 * r₂) * X ^ (eightExp r₁ r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat := by
    rw [hex₁, pow_add]
  have p₂ : (X : ℕ[X]) ^ (r₁ - n₂ - k) *
        X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + (k + 1))).toNat =
      X ^ (t + 1 + (r₂ - n₂)) *
        X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) (n₂ + 1 + k)).toNat := by
    rw [← pow_add, hex₂, pow_add]
  rw [p₁, p₂]
  ring

/-- Lowering `r₁ + 2` to `r₁ + 1`, in both flag positions at once. -/
theorem pow_mul_eightN₅Sum_add_two_fst (r₁ r₂ r₃ n₁ n₂ t : ℕ) (h₂₁ : r₂ ≤ r₁) (hn₂ : n₂ ≤ r₂)
    (hn₁ : n₁ ≤ r₃) (ht : t ≤ r₃ - n₁) :
    X ^ (t + 1) * eightN₅Sum (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) =
      X ^ (2 + 2 * (r₁ - r₂) + 1) * eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) +
        X ^ (r₃ - n₁ - t + (2 + 2 * (r₁ - r₂))) *
          eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) := by
  have hn₂r₁ : n₂ ≤ r₁ := hn₂.trans h₂₁
  rw [eightN₅Sum_eq_sum_range (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (by omega),
    eightN₅Sum_eq_sum_range (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) (by omega),
    eightN₅Sum_eq_sum_range (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (by omega),
    show r₁ + 2 - n₂ = r₁ + 1 - n₂ + 1 from by omega,
    sum_qChoose_succ_mul (X : ℕ[X]) (r₁ + 1 - n₂)
      fun k ↦ X ^ (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  have hex₁ : t + 1 + ((eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + (k + 1))).toNat) =
      r₃ - n₁ - t + (2 + 2 * (r₁ - r₂)) +
        (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k)).toNat := by
    have hZ : eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + (k + 1)) + n₁ + 2 * t + 2 * r₂ =
        eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k) + r₃ + 2 * r₁ + 1 := by
      simp only [eightExp]; push_cast; ring
    have h₀ : 0 ≤ eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k) := eightExp_nonneg
    have h₁ : 0 ≤ eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + (k + 1)) := eightExp_nonneg
    omega
  have hex₂ : t + 1 + k + (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat =
      2 + 2 * (r₁ - r₂) + 1 +
        (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat := by
    have hZ : eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k) + k + t + 2 * r₂ =
        eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) (n₂ + k) + 2 * r₁ + 2 := by
      simp only [eightExp]; push_cast; ring
    have h₀ : 0 ≤ eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) (n₂ + k) := eightExp_nonneg
    have h₁ : 0 ≤ eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k) := eightExp_nonneg
    omega
  have p₁ : (X : ℕ[X]) ^ (t + 1) *
        X ^ (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + (k + 1))).toNat =
      X ^ (r₃ - n₁ - t + (2 + 2 * (r₁ - r₂))) *
        X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k)).toNat := by
    rw [← pow_add, hex₁, pow_add]
  have p₂ : (X : ℕ[X]) ^ (t + 1) * X ^ k *
        X ^ (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat =
      X ^ (2 + 2 * (r₁ - r₂) + 1) *
        X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat := by
    rw [← pow_add, ← pow_add, hex₂, pow_add]
  calc X ^ (t + 1) *
        (qChoose (X : ℕ[X]) (r₁ + 1 - n₂) k *
          (X ^ k * X ^ (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat +
            X ^ (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + (k + 1))).toNat))
      = qChoose (X : ℕ[X]) (r₁ + 1 - n₂) k *
            (X ^ (t + 1) * X ^ k *
              X ^ (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat) +
          qChoose (X : ℕ[X]) (r₁ + 1 - n₂) k *
            (X ^ (t + 1) *
              X ^ (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) (n₂ + (k + 1))).toNat) := by ring
    _ = qChoose (X : ℕ[X]) (r₁ + 1 - n₂) k *
            (X ^ (2 + 2 * (r₁ - r₂) + 1) *
              X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat) +
          qChoose (X : ℕ[X]) (r₁ + 1 - n₂) k *
            (X ^ (r₃ - n₁ - t + (2 + 2 * (r₁ - r₂))) *
              X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k)).toNat) := by
        rw [p₁, p₂]
    _ = X ^ (2 + 2 * (r₁ - r₂) + 1) *
            (qChoose (X : ℕ[X]) (r₁ + 1 - n₂) k *
              X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) (n₂ + k)).toNat) +
          X ^ (r₃ - n₁ - t + (2 + 2 * (r₁ - r₂))) *
            (qChoose (X : ℕ[X]) (r₁ + 1 - n₂) k *
              X ^ (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) (n₂ + k)).toNat) := by
        ring

/--
The block sequence with `W 0 = X ^ D * Nₐ 0` and `W (t+1) = X ^ (3+3r₁) * N₁ t + X ^
(D + (r₂-n₂)) * N_b t`, where `D = 2 + 2 (r₁ - r₂)`.
-/
noncomputable def kernW (r₁ r₂ r₃ n₁ n₂ : ℕ) : ℕ → ℕ[X]
  | 0 => X ^ (2 + 2 * (r₁ - r₂)) * eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + 0)
  | t + 1 =>
      X ^ (3 + 3 * r₁) * eightN₅Sum r₁ r₂ r₃ n₁ n₂ (n₁ + t) +
        X ^ (2 + 2 * (r₁ - r₂) + (r₂ - n₂)) *
          eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t)

@[simp] theorem kernW_zero (r₁ r₂ r₃ n₁ n₂ : ℕ) :
    kernW r₁ r₂ r₃ n₁ n₂ 0 =
      X ^ (2 + 2 * (r₁ - r₂)) * eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + 0) := rfl

theorem kernW_succ (r₁ r₂ r₃ n₁ n₂ t : ℕ) :
    kernW r₁ r₂ r₃ n₁ n₂ (t + 1) =
      X ^ (3 + 3 * r₁) * eightN₅Sum r₁ r₂ r₃ n₁ n₂ (n₁ + t) +
        X ^ (2 + 2 * (r₁ - r₂) + (r₂ - n₂)) *
          eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) := rfl

/--
The block's closed form, premultiplied so that no exponent is truncated: `X ^ t * W t = X ^ D *
Nₐ t`.
-/
theorem pow_mul_kernW (r₁ r₂ r₃ n₁ n₂ : ℕ) (h₂₁ : r₂ ≤ r₁) (hn₂ : n₂ ≤ r₂) (t : ℕ) :
    X ^ t * kernW r₁ r₂ r₃ n₁ n₂ t =
      X ^ (2 + 2 * (r₁ - r₂)) * eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) := by
  cases t with
  | zero => rw [kernW_zero, pow_zero, one_mul]
  | succ t =>
    have h₁ : t + 1 + (3 + 3 * r₁) = 2 + 2 * (r₁ - r₂) + (t + 2 + r₁ + 2 * r₂) := by omega
    have h₂ : t + 1 + (2 + 2 * (r₁ - r₂) + (r₂ - n₂)) =
        2 + 2 * (r₁ - r₂) + (t + 1 + (r₂ - n₂)) := by omega
    calc X ^ (t + 1) * kernW r₁ r₂ r₃ n₁ n₂ (t + 1)
        = X ^ (t + 1 + (3 + 3 * r₁)) * eightN₅Sum r₁ r₂ r₃ n₁ n₂ (n₁ + t) +
            X ^ (t + 1 + (2 + 2 * (r₁ - r₂) + (r₂ - n₂))) *
              eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) := by
          rw [kernW_succ, pow_add, pow_add]; ring
      _ = X ^ (2 + 2 * (r₁ - r₂) + (t + 2 + r₁ + 2 * r₂)) *
              eightN₅Sum r₁ r₂ r₃ n₁ n₂ (n₁ + t) +
            X ^ (2 + 2 * (r₁ - r₂) + (t + 1 + (r₂ - n₂))) *
              eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t) := by rw [h₁, h₂]
      _ = X ^ (2 + 2 * (r₁ - r₂)) *
            (X ^ (t + 2 + r₁ + 2 * r₂) * eightN₅Sum r₁ r₂ r₃ n₁ n₂ (n₁ + t) +
              X ^ (t + 1 + (r₂ - n₂)) *
                eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1) (n₁ + t)) := by
          rw [pow_add, pow_add]; ring
      _ = X ^ (2 + 2 * (r₁ - r₂)) *
            eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1)) := by
          rw [eightN₅Sum_succ_snd r₁ r₂ r₃ n₁ n₂ t h₂₁ hn₂]

/-- The left-hand summand, in terms of the block: `T t = W t + X ^ (M-t) * W (t+1)`. -/
theorem eightN₅Sum_add_two_eq_kernW (r₁ r₂ r₃ n₁ n₂ t : ℕ) (h₂₁ : r₂ ≤ r₁) (hn₂ : n₂ ≤ r₂)
    (hn₁ : n₁ ≤ r₃) (ht : t ≤ r₃ - n₁) :
    eightN₅Sum (r₁ + 2) r₂ r₃ n₁ n₂ (n₁ + t) =
      kernW r₁ r₂ r₃ n₁ n₂ t + X ^ (r₃ - n₁ - t) * kernW r₁ r₂ r₃ n₁ n₂ (t + 1) := by
  refine mul_left_cancel₀ (pow_ne_zero (t + 1) (X_ne_zero (R := ℕ))) ?_
  rw [pow_mul_eightN₅Sum_add_two_fst r₁ r₂ r₃ n₁ n₂ t h₂₁ hn₂ hn₁ ht]
  calc X ^ (2 + 2 * (r₁ - r₂) + 1) * eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t) +
          X ^ (r₃ - n₁ - t + (2 + 2 * (r₁ - r₂))) *
            eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1))
      = X * (X ^ (2 + 2 * (r₁ - r₂)) * eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + t)) +
          X ^ (r₃ - n₁ - t) *
            (X ^ (2 + 2 * (r₁ - r₂)) *
              eightN₅Sum (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ (n₁ + (t + 1))) := by
        rw [pow_succ, pow_add]; ring
    _ = X * (X ^ t * kernW r₁ r₂ r₃ n₁ n₂ t) +
          X ^ (r₃ - n₁ - t) * (X ^ (t + 1) * kernW r₁ r₂ r₃ n₁ n₂ (t + 1)) := by
        rw [pow_mul_kernW r₁ r₂ r₃ n₁ n₂ h₂₁ hn₂ t,
          pow_mul_kernW r₁ r₂ r₃ n₁ n₂ h₂₁ hn₂ (t + 1)]
    _ = X ^ (t + 1) *
          (kernW r₁ r₂ r₃ n₁ n₂ t + X ^ (r₃ - n₁ - t) * kernW r₁ r₂ r₃ n₁ n₂ (t + 1)) := by
        rw [pow_succ]; ring

/-- `KernEightN1`. -/
theorem kernEightN1 : KernEightN1 := by
  intro r₁ r₂ r₃ n₁ n₂ h₃₂ h₂₁ hn₂ hn₁
  have hL : eightFlagSlice (r₁ + 2) r₂ r₃ n₁ n₂ =
      ∑ t ∈ range (r₃ - n₁ + 1), qChoose X (r₃ - n₁) t *
        (kernW r₁ r₂ r₃ n₁ n₂ t + X ^ (r₃ - n₁ - t) * kernW r₁ r₂ r₃ n₁ n₂ (t + 1)) := by
    rw [eightFlagSlice]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [Finset.mem_range] at ht
    rw [eightN₅Sum_add_two_eq_kernW r₁ r₂ r₃ n₁ n₂ t h₂₁ hn₂ hn₁ (by omega)]
  have hR : ∑ t ∈ range (r₃ - n₁ + 1), qChoose X (r₃ - n₁) t *
        (X ^ t * kernW r₁ r₂ r₃ n₁ n₂ t + kernW r₁ r₂ r₃ n₁ n₂ (t + 1)) =
      X ^ (3 + 3 * r₁) * eightFlagSlice r₁ r₂ r₃ n₁ n₂ +
        X ^ (2 + 2 * (r₁ - r₂)) *
          (eightFlagSlice (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ +
            X ^ (r₂ - n₂) * eightFlagSlice (r₁ + 1) (r₂ + 1) r₃ n₁ (n₂ + 1)) := by
    simp only [eightFlagSlice, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [pow_mul_kernW r₁ r₂ r₃ n₁ n₂ h₂₁ hn₂ t, kernW_succ]
    ring
  rw [hL, sum_qChoose_mul_shift_comm (X : ℕ[X]) (r₃ - n₁) (kernW r₁ r₂ r₃ n₁ n₂), hR]

end HJOA3.SumToSum.ThreeTwo
