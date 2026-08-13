module

import QSeriesLib.NumberTheory.HJO.SumToSum.Basic
public import HJOA3.SumToSum.ThreeTwo.Small

/-!
# `thm:sum` at `b = 8`, split by §7's recurrence
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/--
The `X`-exponent of `eightLHS`'s summand, as an integer: the chain quadratic form of §7 in the
coupling order `n₁ – n₂ – n₄ – n₅`.
-/
def eightExp (r₁ r₂ r₃ n₁ n₂ n₄ n₅ : ℕ) : ℤ :=
  n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + r₃ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
    n₁ * n₂ - n₁ * r₂ + n₂ * n₄ - n₂ * r₂ + n₄ * n₅ - n₄ * r₁ + n₅ * r₃ - n₅ * r₁

/-- The `.toNat` in `eightLHS` never clamps at natural arguments. -/
theorem eightExp_nonneg {r₁ r₂ r₃ n₁ n₂ n₄ n₅ : ℕ} : 0 ≤ eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅ := by
  have key : 4 * eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅ =
      (2 * (n₁ : ℤ) - r₂) ^ 2 + (2 * (n₂ : ℤ) - r₂) ^ 2 + (2 * (n₄ : ℤ) - r₁) ^ 2 +
          (2 * (n₅ : ℤ) - r₁) ^ 2 + 4 * (r₃ : ℤ) ^ 2 + 2 * (r₂ : ℤ) ^ 2 + 2 * (r₁ : ℤ) ^ 2 +
        4 * ((n₁ : ℤ) * n₂ + (n₂ : ℤ) * n₄ + (n₄ : ℤ) * n₅ + (n₅ : ℤ) * r₃) := by
    simp only [eightExp]
    ring
  have hcross : (0 : ℤ) ≤ (n₁ : ℤ) * n₂ + (n₂ : ℤ) * n₄ + (n₄ : ℤ) * n₅ + (n₅ : ℤ) * r₃ := by
    positivity
  linarith [sq_nonneg (2 * (n₁ : ℤ) - r₂), sq_nonneg (2 * (n₂ : ℤ) - r₂),
    sq_nonneg (2 * (n₄ : ℤ) - r₁), sq_nonneg (2 * (n₅ : ℤ) - r₁), sq_nonneg (r₃ : ℤ),
    sq_nonneg (r₂ : ℤ), sq_nonneg (r₁ : ℤ)]

/-- The exponent shift along the recurrence's first source, `r₁ ↦ r₁ + 2`. -/
theorem eightExp_toNat_add_two_left {r₁ r₂ r₃ n₁ n₂ n₄ n₅ : ℕ} :
    (eightExp (r₁ + 2) r₂ r₃ n₁ n₂ n₄ n₅).toNat + 2 * n₄ + 2 * n₅ =
      (eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅).toNat + 4 * r₁ + 4 := by
  have hS : 0 ≤ eightExp (r₁ + 2) r₂ r₃ n₁ n₂ n₄ n₅ := eightExp_nonneg
  have h₀ : 0 ≤ eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅ := eightExp_nonneg
  have key : eightExp (r₁ + 2) r₂ r₃ n₁ n₂ n₄ n₅ + 2 * n₄ + 2 * n₅ =
      eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅ + 4 * r₁ + 4 := by
    simp only [eightExp]; push_cast; ring
  omega

/--
The exponent shift along the recurrence's second source, the level-preserving `(r₁, r₂) ↦ (r₁ +
1, r₂ + 1)`.
-/
theorem eightExp_toNat_succ_succ {r₁ r₂ r₃ n₁ n₂ n₄ n₅ : ℕ} :
    (eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ n₄ n₅).toNat + n₁ + n₂ + n₄ + n₅ =
      (eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅).toNat + 2 * r₁ + 2 * r₂ + 2 := by
  have hS : 0 ≤ eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ n₄ n₅ := eightExp_nonneg
  have h₀ : 0 ≤ eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅ := eightExp_nonneg
  have key : eightExp (r₁ + 1) (r₂ + 1) r₃ n₁ n₂ n₄ n₅ + n₁ + n₂ + n₄ + n₅ =
      eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅ + 2 * r₁ + 2 * r₂ + 2 := by
    simp only [eightExp]; push_cast; ring
  omega

/--
The left side of `eight_iff` — §7's quadruple sum `S(r₁, r₂, r₃)`, named so that the recurrence
below can be stated about it.
-/
noncomputable def eightLHS (r₁ r₂ r₃ : ℕ) : ℕ[X] :=
  ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₁ + 1),
  ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
    X ^ (eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅).toNat *
      qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
      extendedQChoose X ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂)

/-- The right side of `eight_iff` — §7's double sum `D(r₁, r₂, r₃)`. -/
noncomputable def eightRHS (r₁ r₂ r₃ : ℕ) : ℕ[X] :=
  ∑ m₁ ∈ range (2 * r₁ + 1), ∑ m₂ ∈ range (2 * r₁ + 1),
    X ^ (r₃ ^ 2 + ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂))) *
      qChoose X (r₁ - r₂ + m₂) m₁ * qChoose X (r₂ + r₃) m₂

/-- `eightLHS` with no extended `q`-binomial. -/
theorem eightLHS_eq_guarded (r₁ r₂ r₃ : ℕ) (h₂₁ : r₂ ≤ r₁) :
    eightLHS r₁ r₂ r₃ =
      ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₁ + 1),
      ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
        X ^ (eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅).toNat *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
          (if n₂ ≤ n₅ then qChoose X (r₁ - n₂) (n₅ - n₂) else 0) := by
  unfold eightLHS
  refine Finset.sum_congr rfl fun n₂ hn₂ ↦ Finset.sum_congr rfl fun n₅ hn₅ ↦
    Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₄ _ ↦ ?_
  simp only [mem_range] at hn₂ hn₅
  congr 1
  split_ifs with h
  · rw [extendedQChoose_of_nonneg (by omega) (by omega)]
    congr 1 <;> omega
  · rw [extendedQChoose_of_neg_left (Or.inr (by omega))]

theorem eight_iff' {r₁ r₂ r₃ : ℕ} (hr₂₁ : r₂ ≤ r₁) (hr₃₂ : r₃ ≤ r₂) :
    Conjecture 2 ![r₁, r₂, r₃] ↔ eightLHS r₁ r₂ r₃ = eightRHS r₁ r₂ r₃ :=
  eight_iff hr₂₁ hr₃₂

/-- §7's recurrence for the quadruple sum. -/
def RecEightLHS : Prop :=
  ∀ r₁ r₂ r₃ : ℕ, r₃ ≤ r₂ → r₂ ≤ r₁ →
    eightLHS (r₁ + 2) r₂ r₃ =
      X ^ (3 + 3 * r₁) * eightLHS r₁ r₂ r₃ +
        X ^ (2 + 2 * (r₁ - r₂)) * eightLHS (r₁ + 1) (r₂ + 1) r₃

def RecEightRHS : Prop :=
  ∀ r₁ r₂ r₃ : ℕ, r₃ ≤ r₂ → r₂ ≤ r₁ →
    eightRHS (r₁ + 2) r₂ r₃ =
      X ^ (3 + 3 * r₁) * eightRHS r₁ r₂ r₃ +
        X ^ (2 + 2 * (r₁ - r₂)) * eightRHS (r₁ + 1) (r₂ + 1) r₃

/--
The two lowest levels of the chamber: the `b = 8` identity at `r₁ = r₂` and at `r₁ = r₂ + 1`.
-/
def BaseEight : Prop :=
  ∀ r₂ r₃ : ℕ, r₃ ≤ r₂ →
    eightLHS r₂ r₂ r₃ = eightRHS r₂ r₂ r₃ ∧
      eightLHS (r₂ + 1) r₂ r₃ = eightRHS (r₂ + 1) r₂ r₃

/-- The induction on the level `r₁ - r₂`. -/
theorem eightLHS_eq_eightRHS_of_rec (hL : RecEightLHS) (hR : RecEightRHS) (hb : BaseEight) :
    ∀ L r₂ r₃ : ℕ, r₃ ≤ r₂ → eightLHS (r₂ + L) r₂ r₃ = eightRHS (r₂ + L) r₂ r₃ := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro r₂ r₃ h₃₂
    match L with
    | 0 => exact (hb r₂ r₃ h₃₂).1
    | 1 => exact (hb r₂ r₃ h₃₂).2
    | (n + 2) =>
      have hstep : r₂ + (n + 2) = r₂ + n + 2 := by omega
      have i₁ : eightLHS (r₂ + n) r₂ r₃ = eightRHS (r₂ + n) r₂ r₃ :=
        ih n (by omega) r₂ r₃ h₃₂
      have i₂ : eightLHS (r₂ + n + 1) (r₂ + 1) r₃ = eightRHS (r₂ + n + 1) (r₂ + 1) r₃ := by
        have hshift : r₂ + n + 1 = r₂ + 1 + n := by omega
        rw [hshift]
        exact ih n (by omega) (r₂ + 1) r₃ (by omega)
      rw [hstep, hL (r₂ + n) r₂ r₃ h₃₂ (by omega), hR (r₂ + n) r₂ r₃ h₃₂ (by omega), i₁, i₂]

/-- The two recurrences and two base levels imply the sum-to-sum conjecture for `b = 8`. -/
theorem eight_of_rec (hL : RecEightLHS) (hR : RecEightRHS) (hb : BaseEight)
    {r₁ r₂ r₃ : ℕ} (hr₂₁ : r₂ ≤ r₁) (hr₃₂ : r₃ ≤ r₂) : Conjecture 2 ![r₁, r₂, r₃] := by
  refine (eight_iff' hr₂₁ hr₃₂).mpr ?_
  have hr₁ : r₁ = r₂ + (r₁ - r₂) := by omega
  rw [hr₁]
  exact eightLHS_eq_eightRHS_of_rec hL hR hb _ r₂ r₃ hr₃₂

end HJOA3.SumToSum.ThreeTwo
