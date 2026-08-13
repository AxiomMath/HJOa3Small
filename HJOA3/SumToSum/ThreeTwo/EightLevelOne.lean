module

public import HJOA3.SumToSum.ThreeTwo.EightInt

/-!
# `BaseEight` at the level `r₁ = r₂ + 1`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/-- The chained term. -/
noncomputable def eightT₁ (r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ n₂ ∈ range (r₂ + 2), ∑ n₅ ∈ range (r₂ + 2),
  ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
    X ^ (eightExp (r₂ + 1) r₂ r₃ n₁ n₂ n₄ n₅).toNat *
      qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X (r₂ + 1) n₅ * qChoose X n₅ n₂

/-- The telescoped term. -/
noncomputable def eightT₂ (r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ n₂ ∈ range (r₂ + 2), ∑ n₅ ∈ range (r₂ + 2),
  ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
    X ^ (eightExp (r₂ + 1) r₂ r₃ n₁ n₂ n₄ n₅ + ((r₂ : ℤ) + 1 - n₂)).toNat *
      qChoose X n₄ n₁ * qChoose X r₃ n₄ *
      extendedQChoose X (r₂ : ℤ) ((n₂ : ℤ) - 1) *
      extendedQChoose X ((r₂ : ℤ) + 1 - n₂) ((n₅ : ℤ) - n₂)

/-- `eightT₁` convolved. -/
noncomputable def eightD₁ (r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ m₁ ∈ range (2 * r₂ + 3), ∑ m₂ ∈ range (2 * r₂ + 3),
    X ^ (r₃ ^ 2 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) + ((r₂ + 1) ^ 2 + m₂ ^ 2 - (r₂ + 1) * m₂))) *
      qChoose X (r₂ + 1 + r₃) m₂ * qChoose X m₂ m₁

/-- `eightT₂` convolved. -/
noncomputable def eightD₂ (r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ m₁ ∈ range (2 * r₂ + 3), ∑ m₂ ∈ range (2 * r₂ + 3),
    X ^ (r₃ ^ 2 + r₃ + 1 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) + m₁) +
        ((r₂ + 1) ^ 2 + (m₂ + 1) ^ 2 - (r₂ + 1) * (m₂ + 1))) *
      qChoose X (r₂ + r₃) m₂ * qChoose X m₂ m₁

/-- `eightD₁` with each summand expanded into the two convolutions. -/
theorem eightD₁_eq_sum_block (r₂ r₃ : ℕ) :
    eightD₁ r₂ r₃ =
      ∑ m₁ ∈ range (2 * r₂ + 3), ∑ m₂ ∈ range (2 * r₂ + 3),
        X ^ (r₃ ^ 2 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) + ((r₂ + 1) ^ 2 + m₂ ^ 2 - (r₂ + 1) * m₂))) *
          (∑ n₄ ∈ range (m₂ + 1),
            X ^ ((r₃ - n₄) * (m₂ - n₄)) * qChoose X r₃ n₄ * qChoose X (r₂ + 1) (m₂ - n₄) *
              (∑ n₁ ∈ range (m₁ + 1),
                X ^ ((n₄ - n₁) * (m₁ - n₁)) * qChoose X n₄ n₁ *
                  qChoose X (m₂ - n₄) (m₁ - n₁))) := by
  rw [eightD₁]
  refine Finset.sum_congr rfl fun m₁ _ ↦ Finset.sum_congr rfl fun m₂ _ ↦ ?_
  rw [sum_vandermonde_block (X : ℤ[X]) (r₂ + 1) r₃ m₁ m₂]
  ring

/--
The box is `[0, r₃] × [0, r₂ + 1]` — the widened one — and it fits inside `range (2 * r₂ + 3)`
because `r₃ ≤ r₂`.
-/
theorem eightT₁_eq_eightD₁ (r₂ r₃ : ℕ) (h₃ : r₃ ≤ r₂) : eightT₁ r₂ r₃ = eightD₁ r₂ r₃ := by
  have hprep : eightT₁ r₂ r₃ =
      ∑ n₂ ∈ range (r₂ + 2), ∑ n₅ ∈ range (r₂ + 2),
      ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
        X ^ (r₃ ^ 2 + ((r₂ ^ 2 + (n₁ + n₂) ^ 2 - r₂ * (n₁ + n₂)) +
            ((r₂ + 1) ^ 2 + (n₄ + n₅) ^ 2 - (r₂ + 1) * (n₄ + n₅)))) *
          X ^ ((n₄ - n₁) * n₂) * X ^ ((r₃ - n₄) * n₅) *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X (r₂ + 1) n₅ * qChoose X n₅ n₂ := by
    rw [eightT₁]
    refine Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_congr rfl fun n₅ _ ↦
      Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₄ hn₄ ↦ ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hn₄
    by_cases hn₁₄ : n₁ ≤ n₄
    · rw [eightExp_toNat_split hn₁₄ hn₄, pow_add, pow_add]
    · rw [qChoose_eq_zero_of_lt (show n₄ < n₁ from by omega)]
      ring
  rw [hprep, eightD₁_eq_sum_block]
  exact sum_box_eq_sum_block (X : ℤ[X]) (fun n k ↦ qChoose X n k)
    (fun _ _ h ↦ qChoose_eq_zero_of_lt h) r₃ (r₂ + 1) (2 * r₂ + 2)
    (fun m₁ m₂ ↦ r₃ ^ 2 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) + ((r₂ + 1) ^ 2 + m₂ ^ 2 - (r₂ + 1) * m₂)))
    (by omega)

/-- Dropping a vanishing first row and column, and reindexing. -/
theorem sum_range_two_shift {M : Type*} [AddCommMonoid M] (n : ℕ) (G : ℕ → ℕ → M)
    (h₀ : ∀ b, G 0 b = 0) (h₀' : ∀ a, G a 0 = 0) :
    (∑ a ∈ range (n + 2), ∑ b ∈ range (n + 2), G a b)
      = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), G (a + 1) (b + 1) := by
  rw [Finset.sum_range_succ' (fun a ↦ ∑ b ∈ range (n + 2), G a b) (n + 1)]
  simp only [h₀, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_range_succ' (fun b ↦ G (a + 1) b) (n + 1), h₀', add_zero]

/-- The shifted exponent split. -/
theorem eightExp_toNat_shift_split {r₂ r₃ n₁ n₂ n₄ n₅ : ℕ} (h₁₄ : n₁ ≤ n₄) (h₄ : n₄ ≤ r₃) :
    (eightExp (r₂ + 1) r₂ r₃ n₁ (n₂ + 1) n₄ (n₅ + 1)
        + ((r₂ : ℤ) + 1 - ((n₂ + 1 : ℕ) : ℤ))).toNat =
      r₃ ^ 2 + r₃ + 1 + ((r₂ ^ 2 + (n₁ + n₂) ^ 2 - r₂ * (n₁ + n₂)) + (n₁ + n₂)) +
          ((r₂ + 1) ^ 2 + (n₄ + n₅ + 1) ^ 2 - (r₂ + 1) * (n₄ + n₅ + 1))
        + (n₄ - n₁) * n₂ + (r₃ - n₄) * n₅ := by
  have hb₁ : r₂ * (n₁ + n₂) ≤ r₂ ^ 2 + (n₁ + n₂) ^ 2 := by
    nlinarith [sq_nonneg (r₂ - (n₁ + n₂)), sq_nonneg ((n₁ + n₂) - r₂)]
  have hb₂ : (r₂ + 1) * (n₄ + n₅ + 1) ≤ (r₂ + 1) ^ 2 + (n₄ + n₅ + 1) ^ 2 := by
    nlinarith [sq_nonneg ((r₂ + 1) - (n₄ + n₅ + 1)), sq_nonneg ((n₄ + n₅ + 1) - (r₂ + 1))]
  have hkey : eightExp (r₂ + 1) r₂ r₃ n₁ (n₂ + 1) n₄ (n₅ + 1)
        + ((r₂ : ℤ) + 1 - ((n₂ + 1 : ℕ) : ℤ)) =
      ((r₃ ^ 2 + r₃ + 1 + ((r₂ ^ 2 + (n₁ + n₂) ^ 2 - r₂ * (n₁ + n₂)) + (n₁ + n₂)) +
          ((r₂ + 1) ^ 2 + (n₄ + n₅ + 1) ^ 2 - (r₂ + 1) * (n₄ + n₅ + 1))
        + (n₄ - n₁) * n₂ + (r₃ - n₄) * n₅ : ℕ) : ℤ) := by
    simp only [eightExp]
    push_cast [Nat.cast_sub hb₁, Nat.cast_sub hb₂, Nat.cast_sub h₁₄, Nat.cast_sub h₄]
    ring
  rw [hkey, Int.toNat_natCast]

/-- `eightD₂` with each summand expanded into the two convolutions. -/
theorem eightD₂_eq_sum_block (r₂ r₃ : ℕ) :
    eightD₂ r₂ r₃ =
      ∑ m₁ ∈ range (2 * r₂ + 3), ∑ m₂ ∈ range (2 * r₂ + 3),
        X ^ (r₃ ^ 2 + r₃ + 1 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) + m₁) +
            ((r₂ + 1) ^ 2 + (m₂ + 1) ^ 2 - (r₂ + 1) * (m₂ + 1))) *
          (∑ n₄ ∈ range (m₂ + 1),
            X ^ ((r₃ - n₄) * (m₂ - n₄)) * qChoose X r₃ n₄ * qChoose X r₂ (m₂ - n₄) *
              (∑ n₁ ∈ range (m₁ + 1),
                X ^ ((n₄ - n₁) * (m₁ - n₁)) * qChoose X n₄ n₁ *
                  qChoose X (m₂ - n₄) (m₁ - n₁))) := by
  rw [eightD₂]
  refine Finset.sum_congr rfl fun m₁ _ ↦ Finset.sum_congr rfl fun m₂ _ ↦ ?_
  rw [sum_vandermonde_block (X : ℤ[X]) r₂ r₃ m₁ m₂]
  ring

theorem eightT₂_eq_eightD₂ (r₂ r₃ : ℕ) (h₃ : r₃ ≤ r₂) : eightT₂ r₂ r₃ = eightD₂ r₂ r₃ := by
  have hprep : eightT₂ r₂ r₃ =
      ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₂ + 1),
      ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
        X ^ (r₃ ^ 2 + r₃ + 1 + ((r₂ ^ 2 + (n₁ + n₂) ^ 2 - r₂ * (n₁ + n₂)) + (n₁ + n₂)) +
            ((r₂ + 1) ^ 2 + (n₄ + n₅ + 1) ^ 2 - (r₂ + 1) * (n₄ + n₅ + 1))) *
          X ^ ((n₄ - n₁) * n₂) * X ^ ((r₃ - n₄) * n₅) *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₅ * qChoose X n₅ n₂ := by
    rw [eightT₂, sum_range_two_shift r₂ _ ?_ ?_]
    · refine Finset.sum_congr rfl fun n₂ hn₂ ↦ Finset.sum_congr rfl fun n₅ hn₅ ↦
        Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₄ hn₄ ↦ ?_
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hn₂ hn₅ hn₄
      have hx₁ : extendedQChoose (X : ℤ[X]) (r₂ : ℤ) (((n₂ + 1 : ℕ) : ℤ) - 1)
          = qChoose X r₂ n₂ := by
        rw [show (((n₂ + 1 : ℕ) : ℤ) - 1) = ((n₂ : ℕ) : ℤ) from by push_cast; ring,
          extendedQChoose_natCast]
      by_cases hn₁₄ : n₁ ≤ n₄
      · by_cases h₂₅ : n₂ ≤ n₅
        · have hx₂ : extendedQChoose (X : ℤ[X]) ((r₂ : ℤ) + 1 - ((n₂ + 1 : ℕ) : ℤ))
              (((n₅ + 1 : ℕ) : ℤ) - ((n₂ + 1 : ℕ) : ℤ)) = qChoose X (r₂ - n₂) (n₅ - n₂) := by
            rw [show ((r₂ : ℤ) + 1 - ((n₂ + 1 : ℕ) : ℤ)) = ((r₂ - n₂ : ℕ) : ℤ) from by
                  push_cast [Nat.cast_sub hn₂]; ring,
              show (((n₅ + 1 : ℕ) : ℤ) - ((n₂ + 1 : ℕ) : ℤ)) = ((n₅ - n₂ : ℕ) : ℤ) from by
                  push_cast [Nat.cast_sub h₂₅]; ring,
              extendedQChoose_natCast]
          rw [eightExp_toNat_shift_split hn₁₄ hn₄, hx₁, hx₂, pow_add, pow_add,
            mul_assoc _ (qChoose (X : ℤ[X]) r₂ n₂) (qChoose X (r₂ - n₂) (n₅ - n₂)),
            show qChoose (X : ℤ[X]) r₂ n₂ * qChoose X (r₂ - n₂) (n₅ - n₂)
              = qChoose X r₂ n₅ * qChoose X n₅ n₂ from (qChoose_mul_semiring X h₂₅).symm]
          ring
        · rw [extendedQChoose_of_neg_left (q := (X : ℤ[X]))
              (n := (r₂ : ℤ) + 1 - ((n₂ + 1 : ℕ) : ℤ))
              (r := ((n₅ + 1 : ℕ) : ℤ) - ((n₂ + 1 : ℕ) : ℤ)) (Or.inr (by omega)),
            qChoose_eq_zero_of_lt (show n₅ < n₂ from by omega)]
          ring
      · rw [qChoose_eq_zero_of_lt (show n₄ < n₁ from by omega)]
        ring
    · intro n₅
      refine Finset.sum_eq_zero fun n₁ _ ↦ Finset.sum_eq_zero fun n₄ _ ↦ ?_
      rw [extendedQChoose_of_neg_left (q := (X : ℤ[X])) (Or.inr (by omega))]
      ring
    · intro n₂
      refine Finset.sum_eq_zero fun n₁ _ ↦ Finset.sum_eq_zero fun n₄ _ ↦ ?_
      rcases Nat.eq_zero_or_pos n₂ with h | h
      · subst h
        rw [extendedQChoose_of_neg_left (q := (X : ℤ[X])) (Or.inr (by omega))]
        ring
      · rw [extendedQChoose_of_neg_left (q := (X : ℤ[X])) (n := (r₂ : ℤ) + 1 - n₂)
          (Or.inr (by omega))]
        ring
  rw [hprep, eightD₂_eq_sum_block]
  exact sum_box_eq_sum_block (X : ℤ[X]) (fun n k ↦ qChoose X n k)
    (fun _ _ h ↦ qChoose_eq_zero_of_lt h) r₃ r₂ (2 * r₂ + 2)
    (fun m₁ m₂ ↦ r₃ ^ 2 + r₃ + 1 + ((r₂ ^ 2 + m₁ ^ 2 - r₂ * m₁) + m₁) +
      ((r₂ + 1) ^ 2 + (m₂ + 1) ^ 2 - (r₂ + 1) * (m₂ + 1)))
    (by omega)

/--
`qChoose_succ_succ'` restated so that it holds at `k = 0` too: there the lowered index is `-1`,
where the extended binomial is `0` and the identity reads `1 = 1`.
-/
theorem qChoose_succ_left_extended {R : Type*} [CommSemiring R] (q : R) (n k : ℕ) :
    qChoose q (n + 1) k
      = qChoose q n k + q ^ (n + 1 - k) * extendedQChoose q (n : ℤ) ((k : ℤ) - 1) := by
  cases k with
  | zero => simp
  | succ j =>
    rw [qChoose_succ_succ', show ((j + 1 : ℕ) : ℤ) - 1 = ((j : ℕ) : ℤ) from by omega,
      extendedQChoose_natCast, Nat.succ_sub_succ]
    ring

theorem eight_pascal_termwise {r₂ r₃ n₁ n₂ n₄ n₅ : ℕ} (hn₂ : n₂ ≤ r₂ + 1) :
    (X : ℤ[X]) ^ (eightExp (r₂ + 1) r₂ r₃ n₁ n₂ n₄ n₅).toNat *
        qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
        extendedQChoose X (((r₂ + 1 : ℕ) : ℤ) - n₂) ((n₅ : ℤ) - n₂)
      = X ^ (eightExp (r₂ + 1) r₂ r₃ n₁ n₂ n₄ n₅).toNat *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X (r₂ + 1) n₅ * qChoose X n₅ n₂
        - X ^ (eightExp (r₂ + 1) r₂ r₃ n₁ n₂ n₄ n₅ + ((r₂ : ℤ) + 1 - n₂)).toNat *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * extendedQChoose X (r₂ : ℤ) ((n₂ : ℤ) - 1) *
          extendedQChoose X ((r₂ : ℤ) + 1 - n₂) ((n₅ : ℤ) - n₂) := by
  rw [show (((r₂ + 1 : ℕ) : ℤ) - n₂) = (r₂ : ℤ) + 1 - n₂ from by omega]
  by_cases h₂₅ : n₂ ≤ n₅
  · by_cases hn₁₄ : n₁ ≤ n₄
    · have hE : 0 ≤ eightExp (r₂ + 1) r₂ r₃ n₁ n₂ n₄ n₅ := eightExp_nonneg
      have hext : extendedQChoose (X : ℤ[X]) ((r₂ : ℤ) + 1 - n₂) ((n₅ : ℤ) - n₂)
          = qChoose X (r₂ + 1 - n₂) (n₅ - n₂) := by
        rw [show ((r₂ : ℤ) + 1 - n₂) = ((r₂ + 1 - n₂ : ℕ) : ℤ) from by omega,
          show ((n₅ : ℤ) - n₂) = ((n₅ - n₂ : ℕ) : ℤ) from by omega, extendedQChoose_natCast]
      rw [Int.toNat_add hE (by omega), show ((r₂ : ℤ) + 1 - n₂).toNat = r₂ + 1 - n₂ from by omega,
        pow_add, hext, mul_assoc _ (qChoose (X : ℤ[X]) (r₂ + 1) n₅) (qChoose X n₅ n₂),
        qChoose_mul_semiring X h₂₅, qChoose_succ_left_extended (X : ℤ[X]) r₂ n₂]
      ring
    · rw [qChoose_eq_zero_of_lt (show n₄ < n₁ from by omega)]
      ring
  · rw [extendedQChoose_of_neg_left (q := (X : ℤ[X])) (n := (r₂ : ℤ) + 1 - n₂)
      (r := (n₅ : ℤ) - n₂) (Or.inr (by omega)),
    qChoose_eq_zero_of_lt (show n₅ < n₂ from by omega)]
    ring

theorem eightLHSInt_eq_eightT₁_sub_eightT₂ (r₂ r₃ : ℕ) :
    eightLHSInt (r₂ + 1) r₂ r₃ = eightT₁ r₂ r₃ - eightT₂ r₂ r₃ := by
  have hwiden : eightLHSInt (r₂ + 1) r₂ r₃ =
      ∑ n₂ ∈ range (r₂ + 2), ∑ n₅ ∈ range (r₂ + 1 + 1),
      ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
        X ^ (eightExp (r₂ + 1) r₂ r₃ n₁ n₂ n₄ n₅).toNat *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
          extendedQChoose X (((r₂ + 1 : ℕ) : ℤ) - n₂) ((n₅ : ℤ) - n₂) := by
    have hsub : range (r₂ + 1) ⊆ range (r₂ + 2) :=
      Finset.range_subset.2 fun x hx ↦ Finset.mem_range.2 (by omega)
    rw [eightLHSInt]
    refine Finset.sum_subset hsub fun n₂ _ hn₂ ↦ ?_
    simp only [Finset.mem_range, not_lt] at hn₂
    refine Finset.sum_eq_zero fun n₅ _ ↦ Finset.sum_eq_zero fun n₁ _ ↦
      Finset.sum_eq_zero fun n₄ _ ↦ ?_
    rw [qChoose_eq_zero_of_lt (show r₂ < n₂ from by omega)]
    ring
  rw [hwiden, eightT₁, eightT₂]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n₂ hn₂ ↦ Finset.sum_congr rfl fun n₅ _ ↦
    Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₄ hn₄ ↦ ?_
  simp only [Finset.mem_range] at hn₂ hn₄
  exact eight_pascal_termwise (by omega)

/-- The residual identity at level `r₁ = r₂ + 1`. -/
def ReducedEight : Prop :=
  ∀ r₂ r₃ : ℕ, r₃ ≤ r₂ → eightD₁ r₂ r₃ - eightD₂ r₂ r₃ = eightRHSInt (r₂ + 1) r₂ r₃

/-- `ReducedEight` implies `BaseEight`. -/
theorem baseEight_of_reduced (hR : ReducedEight) : BaseEight :=
  baseEight_of_succ_int fun r₂ r₃ h₃ ↦ by
    rw [eightLHSInt_eq_eightT₁_sub_eightT₂ r₂ r₃, eightT₁_eq_eightD₁ r₂ r₃ h₃,
      eightT₂_eq_eightD₂ r₂ r₃ h₃, hR r₂ r₃ h₃]

end HJOA3.SumToSum.ThreeTwo
