module

public import HJOA3.FibrationSeven
public import HJOA3.SumToSum.ThreeTwo.EightRec

/-!
# `thm:main` for `b = 8`: the fibration chain at `K = 3`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/-- The sum-to-sum conjecture for `b = 8`. -/
def SumToSumEight : Prop :=
  ∀ {r₁ r₂ r₃ : ℕ}, r₂ ≤ r₁ → r₃ ≤ r₂ → SumToSum.ThreeTwo.Conjecture 2 ![r₁, r₂, r₃]

/-- `SumToSumEight` splits along §7's recurrence. -/
theorem sumToSumEight_of_rec (hL : SumToSum.ThreeTwo.RecEightLHS)
    (hR : SumToSum.ThreeTwo.RecEightRHS) (hb : SumToSum.ThreeTwo.BaseEight) :
    SumToSumEight :=
  fun h₂₁ h₃₂ ↦ SumToSum.ThreeTwo.eight_of_rec hL hR hb h₂₁ h₃₂

/--
The seven coordinates of `splitEight.symm`, as `rfl` lemmas: the gaps of `⟨3, 8⟩` are `1, 2, 4,
5, 7, 10, 13`, with the first four free and `7, 10, 13` pinned to `r₃, r₂, r₁`.
-/
theorem splitEight_symm_gap_one (r : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    (splitEight.symm (r, v)) g%1 = v 0 := rfl

theorem splitEight_symm_gap_two (r : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    (splitEight.symm (r, v)) g%2 = v 1 := rfl

theorem splitEight_symm_gap_four (r : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    (splitEight.symm (r, v)) g%4 = v 2 := rfl

theorem splitEight_symm_gap_five (r : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    (splitEight.symm (r, v)) g%5 = v 3 := rfl

theorem splitEight_symm_gap_seven (r : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    (splitEight.symm (r, v)) g%7 = r 2 := rfl

theorem splitEight_symm_gap_ten (r : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    (splitEight.symm (r, v)) g%10 = r 1 := rfl

theorem splitEight_symm_gap_thirteen (r : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    (splitEight.symm (r, v)) g%13 = r 0 := rfl

/-- `restratifiedEight` vanishes off the box. -/
theorem restratifiedEight_split_eq_zero (r : Fin 3 → ℤ) (v : Fin 4 → ℤ)
    (h : ¬(0 ≤ v 0 ∧ v 0 ≤ r 2 ∧ 0 ≤ v 1 ∧ v 1 ≤ r 1 ∧
      0 ≤ v 2 ∧ v 2 ≤ r 2 ∧ 0 ≤ v 3 ∧ v 3 ≤ r 0)) :
    restratifiedEight (splitEight.symm (r, v)) = 0 := by
  simp only [restratifiedEight, splitEight_symm_gap_one, splitEight_symm_gap_two,
    splitEight_symm_gap_four, splitEight_symm_gap_five, splitEight_symm_gap_seven,
    splitEight_symm_gap_ten, splitEight_symm_gap_thirteen]
  rcases lt_or_ge (v 1) 0 with h1 | h1
  · rw [extendedQChoose_eq_zero (A := r 1) (B := v 1) (Or.inr h1)]
    ring
  rcases lt_or_ge (r 1) (v 1) with h1' | h1'
  · rw [extendedQChoose_eq_zero_of_lt (A := r 1) (B := v 1) h1']
    ring
  rcases lt_or_ge (v 2) 0 with h2 | h2
  · rw [extendedQChoose_eq_zero (A := r 2) (B := v 2) (Or.inr h2)]
    ring
  rcases lt_or_ge (r 2) (v 2) with h2' | h2'
  · rw [extendedQChoose_eq_zero_of_lt (A := r 2) (B := v 2) h2']
    ring
  rcases lt_or_ge (v 0) 0 with h0 | h0
  · rw [extendedQChoose_eq_zero (A := v 2) (B := v 0) (Or.inr h0)]
    ring
  rcases lt_or_ge (r 2) (v 0) with h0' | h0'
  · rw [extendedQChoose_eq_zero_of_lt (A := v 2) (B := v 0) (by omega)]
    ring
  rcases lt_or_ge (v 3) 0 with h3 | h3
  · rw [extendedQChoose_eq_zero (A := r 0 - v 1) (B := v 3 - v 1) (Or.inr (by omega))]
    ring
  rcases lt_or_ge (r 0) (v 3) with h3' | h3'
  · rw [extendedQChoose_eq_zero_of_lt (A := r 0 - v 1) (B := v 3 - v 1) (by omega)]
    ring
  exact absurd ⟨h0, h0', h1, h1', h2, h2', h3, h3'⟩ h

/--
The vanishing that pulls the outer sum back to `ℕ`, now with three disjuncts: a negative `r₁`
kills `1/(q)_{r₁}`, a negative `r₂` kills `qbinom{r₁}{r₂}`, a negative `r₃` kills
`qbinom{r₂}{r₃}`.
-/
theorem restratifiedEight_split_eq_zero_of_outer {r : Fin 3 → ℤ}
    (hr : r 0 < 0 ∨ r 1 < 0 ∨ r 2 < 0) (v : Fin 4 → ℤ) :
    restratifiedEight (splitEight.symm (r, v)) = 0 := by
  simp only [restratifiedEight, splitEight_symm_gap_seven, splitEight_symm_gap_ten,
    splitEight_symm_gap_thirteen]
  rcases hr with h | h | h
  · rw [extendedSelfQPochhammerInv_of_neg h]
    ring
  · rw [extendedQChoose_eq_zero (A := r 0) (B := r 1) (Or.inr h)]
    ring
  · rw [extendedQChoose_eq_zero (A := r 1) (B := r 2) (Or.inr h)]
    ring

/-- The outer sum runs over `Fin 3 → ℕ`. -/
theorem zNat_eight_outer :
    HJO.zNat 3 8 = ∑' w : Fin 3 → ℕ, ∑' v : Fin 4 → ℤ,
      restratifiedEight (splitEight.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)), v))).toNat := by
  rw [zNat_eight_fibred]
  refine (Function.Injective.tsum_eq (g := fun w : Fin 3 → ℕ ↦ fun j ↦ (w j : ℤ)) ?_ ?_).symm
  · intro w w' hww
    funext j
    exact Nat.cast_injective (congrFun hww j)
  · intro r hr
    by_cases hnn : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2
    · exact ⟨fun j ↦ (r j).toNat, funext fun j ↦ by
        fin_cases j
        · exact Int.toNat_of_nonneg hnn.1
        · exact Int.toNat_of_nonneg hnn.2.1
        · exact Int.toNat_of_nonneg hnn.2.2⟩
    · refine absurd ?_ hr
      have hneg : r 0 < 0 ∨ r 1 < 0 ∨ r 2 < 0 := by
        rcases not_and_or.mp hnn with h | h
        · exact Or.inl (by omega)
        rcases not_and_or.mp h with h | h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      have hz : ∀ v : Fin 4 → ℤ, restratifiedEight (splitEight.symm (r, v)) *
          X ^ (HJO.Q 3 8 (splitEight.symm (r, v))).toNat = 0 :=
        fun v ↦ by rw [restratifiedEight_split_eq_zero_of_outer hneg v, zero_mul]
      simp only [hz, tsum_zero]

/--
The inner `tsum` is a finite box sum, over `[0, r₃] × [0, r₂] × [0, r₃] × [0, r₁]` — the bounds
of `lhs_eight`, in `splitEight`'s coordinate order `n₁, n₂, n₄, n₅`.
-/
theorem inner_eight_eq_sum (r : Fin 3 → ℤ) :
    (∑' v : Fin 4 → ℤ, restratifiedEight (splitEight.symm (r, v)) *
        X ^ (HJO.Q 3 8 (splitEight.symm (r, v))).toNat) =
      ∑ v ∈ Fintype.piFinset ![Finset.Icc (0 : ℤ) (r 2), Finset.Icc (0 : ℤ) (r 1),
          Finset.Icc (0 : ℤ) (r 2), Finset.Icc (0 : ℤ) (r 0)],
        restratifiedEight (splitEight.symm (r, v)) *
          X ^ (HJO.Q 3 8 (splitEight.symm (r, v))).toNat := by
  refine tsum_eq_sum fun v hv ↦ ?_
  have h : ¬(0 ≤ v 0 ∧ v 0 ≤ r 2 ∧ 0 ≤ v 1 ∧ v 1 ≤ r 1 ∧
      0 ≤ v 2 ∧ v 2 ≤ r 2 ∧ 0 ≤ v 3 ∧ v 3 ≤ r 0) := fun hc ↦
    hv ((mem_piFinset_fin_four _ _ _ _ v).mpr
      ⟨Finset.mem_Icc.mpr ⟨hc.1, hc.2.1⟩, Finset.mem_Icc.mpr ⟨hc.2.2.1, hc.2.2.2.1⟩,
       Finset.mem_Icc.mpr ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1⟩,
       Finset.mem_Icc.mpr ⟨hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2⟩⟩)
  rw [restratifiedEight_split_eq_zero r v h, zero_mul]

/-- The termwise identity inside the box. -/
theorem restratifiedEight_split_of_mem (w : Fin 3 → ℕ) (v : Fin 4 → ℤ)
    (h0 : 0 ≤ v 0) (h1 : 0 ≤ v 1) (h2 : 0 ≤ v 2) :
    restratifiedEight (splitEight.symm ((fun j ↦ (w j : ℤ)), v)) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
          qChoose (X : ℤ⟦X⟧) (w 1) (w 2) *
        (qChoose (X : ℤ⟦X⟧) (v 2).toNat (v 0).toNat *
          qChoose (X : ℤ⟦X⟧) (w 2) (v 2).toNat *
          qChoose (X : ℤ⟦X⟧) (w 1) (v 1).toNat *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - v 1) (v 3 - v 1)) := by
  simp only [restratifiedEight, splitEight_symm_gap_one, splitEight_symm_gap_two,
    splitEight_symm_gap_four, splitEight_symm_gap_five, splitEight_symm_gap_seven,
    splitEight_symm_gap_ten, splitEight_symm_gap_thirteen,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 0 : ℤ) from by positivity)
      (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity),
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity)
      (show (0 : ℤ) ≤ (w 2 : ℤ) from by positivity),
    extendedQChoose_of_nonneg h2 h0,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 2 : ℤ) from by positivity) h2,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity) h1,
    Int.toNat_natCast]

/-- The `ℤ → ℕ` reindex of the box, coordinatewise as at `b = 7`. -/
theorem inner_eight_reindex (w : Fin 3 → ℕ) :
    (∑ v ∈ Fintype.piFinset ![Finset.Icc (0 : ℤ) (w 2 : ℤ), Finset.Icc (0 : ℤ) (w 1 : ℤ),
          Finset.Icc (0 : ℤ) (w 2 : ℤ), Finset.Icc (0 : ℤ) (w 0 : ℤ)],
        restratifiedEight (splitEight.symm ((fun j ↦ (w j : ℤ)), v)) *
          X ^ (HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
      ∑ u ∈ Fintype.piFinset ![Finset.range (w 2 + 1), Finset.range (w 1 + 1),
          Finset.range (w 2 + 1), Finset.range (w 0 + 1)],
        restratifiedEight (splitEight.symm ((fun j ↦ (w j : ℤ)), fun j ↦ (u j : ℤ))) *
          X ^ (HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)),
            fun j ↦ (u j : ℤ)))).toNat := by
  refine Finset.sum_nbij'
    (i := fun v : Fin 4 → ℤ ↦ fun j ↦ (v j).toNat)
    (j := fun u : Fin 4 → ℕ ↦ fun j ↦ (u j : ℤ)) ?hi ?hj ?left ?right ?h
  · intro v hv
    obtain ⟨h0, h1, h2, h3⟩ := (mem_piFinset_fin_four _ _ _ _ v).mp hv
    rw [Finset.mem_Icc] at h0 h1 h2 h3
    exact (mem_piFinset_fin_four _ _ _ _ _).mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega),
       Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  · intro u hu
    obtain ⟨h0, h1, h2, h3⟩ := (mem_piFinset_fin_four _ _ _ _ u).mp hu
    rw [Finset.mem_range] at h0 h1 h2 h3
    exact (mem_piFinset_fin_four _ _ _ _ _).mpr
      ⟨Finset.mem_Icc.mpr ⟨by positivity, by omega⟩,
       Finset.mem_Icc.mpr ⟨by positivity, by omega⟩,
       Finset.mem_Icc.mpr ⟨by positivity, by omega⟩,
       Finset.mem_Icc.mpr ⟨by positivity, by omega⟩⟩
  · intro v hv
    obtain ⟨h0, h1, h2, h3⟩ := (mem_piFinset_fin_four _ _ _ _ v).mp hv
    rw [Finset.mem_Icc] at h0 h1 h2 h3
    exact funext fun i ↦ by
      fin_cases i <;> [exact Int.toNat_of_nonneg h0.1; exact Int.toNat_of_nonneg h1.1;
        exact Int.toNat_of_nonneg h2.1; exact Int.toNat_of_nonneg h3.1]
  · intro u _
    funext i
    simp
  · intro v hv
    obtain ⟨h0, h1, h2, h3⟩ := (mem_piFinset_fin_four _ _ _ _ v).mp hv
    rw [Finset.mem_Icc] at h0 h1 h2 h3
    have hv' : (fun j ↦ (((v j).toNat : ℕ) : ℤ)) = v :=
      funext fun i ↦ by
        fin_cases i <;> [exact Int.toNat_of_nonneg h0.1; exact Int.toNat_of_nonneg h1.1;
          exact Int.toNat_of_nonneg h2.1; exact Int.toNat_of_nonneg h3.1]
    rw [hv']

/-- The inner sum, factored. -/
theorem inner_eight_factored (w : Fin 3 → ℕ) :
    (∑' v : Fin 4 → ℤ, restratifiedEight (splitEight.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
          qChoose (X : ℤ⟦X⟧) (w 1) (w 2) *
        ∑ u ∈ Fintype.piFinset ![Finset.range (w 2 + 1), Finset.range (w 1 + 1),
            Finset.range (w 2 + 1), Finset.range (w 0 + 1)],
          qChoose (X : ℤ⟦X⟧) (u 2) (u 0) * qChoose (X : ℤ⟦X⟧) (w 2) (u 2) *
            qChoose (X : ℤ⟦X⟧) (w 1) (u 1) *
            HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - (u 1 : ℤ))
              ((u 3 : ℤ) - (u 1 : ℤ)) *
            X ^ (HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)),
              fun j ↦ (u j : ℤ)))).toNat := by
  rw [inner_eight_eq_sum, inner_eight_reindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [restratifiedEight_split_of_mem w (fun j ↦ (u j : ℤ))
    (by positivity) (by positivity) (by positivity)]
  simp only [Int.toNat_natCast]
  ring

/-- The box sum as a quadruple sum, in `lhs_eight`'s summation order. -/
theorem inner_eight_quad (w : Fin 3 → ℕ) :
    (∑ u ∈ Fintype.piFinset ![Finset.range (w 2 + 1), Finset.range (w 1 + 1),
          Finset.range (w 2 + 1), Finset.range (w 0 + 1)],
        qChoose (X : ℤ⟦X⟧) (u 2) (u 0) * qChoose (X : ℤ⟦X⟧) (w 2) (u 2) *
          qChoose (X : ℤ⟦X⟧) (w 1) (u 1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - (u 1 : ℤ))
            ((u 3 : ℤ) - (u 1 : ℤ)) *
          X ^ (HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)),
            fun j ↦ (u j : ℤ)))).toNat) =
      ∑ n₂ ∈ Finset.range (w 1 + 1), ∑ n₅ ∈ Finset.range (w 0 + 1),
      ∑ n₁ ∈ Finset.range (w 2 + 1), ∑ n₄ ∈ Finset.range (w 2 + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + (w 2 : ℤ) ^ 2 + (w 1 : ℤ) ^ 2 +
            (w 0 : ℤ) ^ 2 + n₁ * n₂ - n₁ * (w 1 : ℤ) + n₂ * n₄ - n₂ * (w 1 : ℤ) +
            n₄ * n₅ - n₄ * (w 0 : ℤ) + n₅ * (w 2 : ℤ) - n₅ * (w 0 : ℤ))).toNat *
          qChoose (X : ℤ⟦X⟧) n₄ n₁ * qChoose (X : ℤ⟦X⟧) (w 2) n₄ *
          qChoose (X : ℤ⟦X⟧) (w 1) n₂ *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - n₂) ((n₅ : ℤ) - n₂) := by
  rw [sum_piFinset_fin_four, Finset.sum_comm,
    Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_comm,
    Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_comm]
  refine Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_congr rfl fun n₅ _ ↦
    Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₄ _ ↦ ?_
  have hQ : HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)),
      fun j ↦ ((![n₁, n₂, n₄, n₅] j : ℕ) : ℤ))) =
      (n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + (w 2 : ℤ) ^ 2 + (w 1 : ℤ) ^ 2 + (w 0 : ℤ) ^ 2 +
        n₁ * n₂ - n₁ * (w 1 : ℤ) + n₂ * n₄ - n₂ * (w 1 : ℤ) + n₄ * n₅ - n₄ * (w 0 : ℤ) +
        n₅ * (w 2 : ℤ) - n₅ * (w 0 : ℤ)) := by
    rw [SumToSum.ThreeTwo.Q_three_eight, splitEight_symm_gap_one, splitEight_symm_gap_two,
      splitEight_symm_gap_four, splitEight_symm_gap_five, splitEight_symm_gap_seven,
      splitEight_symm_gap_ten, splitEight_symm_gap_thirteen]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem inner_eight_transport (he : SumToSumEight) (w : Fin 3 → ℕ)
    (h21 : w 1 ≤ w 0) (h32 : w 2 ≤ w 1) :
    (∑ n₂ ∈ Finset.range (w 1 + 1), ∑ n₅ ∈ Finset.range (w 0 + 1),
      ∑ n₁ ∈ Finset.range (w 2 + 1), ∑ n₄ ∈ Finset.range (w 2 + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + (w 2 : ℤ) ^ 2 + (w 1 : ℤ) ^ 2 +
            (w 0 : ℤ) ^ 2 + n₁ * n₂ - n₁ * (w 1 : ℤ) + n₂ * n₄ - n₂ * (w 1 : ℤ) +
            n₄ * n₅ - n₄ * (w 0 : ℤ) + n₅ * (w 2 : ℤ) - n₅ * (w 0 : ℤ))).toNat *
          qChoose (X : ℤ⟦X⟧) n₄ n₁ * qChoose (X : ℤ⟦X⟧) (w 2) n₄ *
          qChoose (X : ℤ⟦X⟧) (w 1) n₂ *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - n₂) ((n₅ : ℤ) - n₂)) =
      toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 2 w m) := by
  have h1 : w = ![w 0, w 1, w 2] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, SumToSum.ThreeTwo.rhs_eight h21 h32,
    ← (SumToSum.ThreeTwo.eight_iff h21 h32).mp (he h21 h32)]
  simp only [map_sum, map_mul, map_pow, toSeries_X, toSeries_qChoose,
    toSeries_extendedQChoose, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

end HJOA3
