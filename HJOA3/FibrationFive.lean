module

public import HJOA3.Fibration
public import HJOA3.SumToSum.ThreeTwo.Small

/-!
# `thm:main` for `b = 5`: the fibration chain at `K = 2`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/--
The four coordinates of `splitFive.symm`, as `rfl` lemmas: the gaps of `⟨3, 5⟩` are `1, 2, 4,
7`, with `1, 2` free and `4, 7` pinned to `r₂, r₁`.
-/
theorem splitFive_symm_gap_one (r v : Fin 2 → ℤ) : (splitFive.symm (r, v)) g%1 = v 0 := rfl

theorem splitFive_symm_gap_two (r v : Fin 2 → ℤ) : (splitFive.symm (r, v)) g%2 = v 1 := rfl

theorem splitFive_symm_gap_four (r v : Fin 2 → ℤ) : (splitFive.symm (r, v)) g%4 = r 1 := rfl

theorem splitFive_symm_gap_seven (r v : Fin 2 → ℤ) : (splitFive.symm (r, v)) g%7 = r 0 := rfl

/-- `restratifiedFive` vanishes off the box. -/
theorem restratifiedFive_split_eq_zero (r v : Fin 2 → ℤ)
    (h : ¬(0 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 0 ≤ r 1 ∧ v 1 ≤ r 0)) :
    restratifiedFive (splitFive.symm (r, v)) = 0 := by
  simp only [restratifiedFive, splitFive_symm_gap_one, splitFive_symm_gap_two,
    splitFive_symm_gap_four, splitFive_symm_gap_seven]
  rcases lt_or_ge (v 0) 0 with h1 | h1
  · rw [extendedQChoose_eq_zero (A := r 1) (B := v 0) (Or.inr h1)]
    ring
  rcases lt_or_ge (v 1) 0 with h2 | h2
  · rw [extendedQChoose_eq_zero (A := r 0) (B := v 1) (Or.inr h2)]
    ring
  rcases lt_or_ge (r 1) (v 0) with h41 | h41
  · rw [extendedQChoose_eq_zero_of_lt (A := r 1) (B := v 0) h41]
    ring
  rcases lt_or_ge (r 0) (v 1) with h72 | h72
  · rw [extendedQChoose_eq_zero_of_lt (A := r 0) (B := v 1) h72]
    ring
  exact absurd ⟨h1, h2, h41, h72⟩ h

/-- The inner summand of `zNat_five_fibred` is supported in the box. -/
theorem support_inner_five (r : Fin 2 → ℤ) :
    (Function.support fun v : Fin 2 → ℤ ↦ restratifiedFive (splitFive.symm (r, v)) *
        X ^ (HJO.Q 3 5 (splitFive.symm (r, v))).toNat) ⊆
      {v | 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 0 ≤ r 1 ∧ v 1 ≤ r 0} := by
  intro v hv
  by_contra hc
  exact hv (by simp only [restratifiedFive_split_eq_zero r v hc, zero_mul])

/-- The vanishing that pulls the outer sum back to `ℕ`. -/
theorem restratifiedFive_split_eq_zero_of_outer {r : Fin 2 → ℤ} (hr : r 0 < 0 ∨ r 1 < 0)
    (v : Fin 2 → ℤ) :
    restratifiedFive (splitFive.symm (r, v)) = 0 := by
  simp only [restratifiedFive, splitFive_symm_gap_one, splitFive_symm_gap_two,
    splitFive_symm_gap_four, splitFive_symm_gap_seven]
  rcases hr with h | h
  · rw [extendedSelfQPochhammerInv_of_neg h]
    ring
  · rw [extendedQChoose_eq_zero (A := r 0) (B := r 1) (Or.inr h)]
    ring

/-- The outer sum runs over `Fin 2 → ℕ`. -/
theorem zNat_five_outer :
    HJO.zNat 3 5 = ∑' w : Fin 2 → ℕ, ∑' v : Fin 2 → ℤ,
      restratifiedFive (splitFive.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)), v))).toNat := by
  rw [zNat_five_fibred]
  refine (Function.Injective.tsum_eq (g := fun w : Fin 2 → ℕ ↦ fun j ↦ (w j : ℤ)) ?_ ?_).symm
  · intro w w' hww
    funext j
    exact Nat.cast_injective (congrFun hww j)
  · intro r hr
    by_cases hnn : 0 ≤ r 0 ∧ 0 ≤ r 1
    · exact ⟨fun j ↦ (r j).toNat, funext fun j ↦ by
        fin_cases j
        · exact Int.toNat_of_nonneg hnn.1
        · exact Int.toNat_of_nonneg hnn.2⟩
    · refine absurd ?_ hr
      have hneg : r 0 < 0 ∨ r 1 < 0 := by
        rcases not_and_or.mp hnn with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hz : ∀ v : Fin 2 → ℤ, restratifiedFive (splitFive.symm (r, v)) *
          X ^ (HJO.Q 3 5 (splitFive.symm (r, v))).toNat = 0 :=
        fun v ↦ by rw [restratifiedFive_split_eq_zero_of_outer hneg v, zero_mul]
      simp only [hz, tsum_zero]

/-- Membership in a `Fin 2` box with *distinct* bounds, spelled out. -/
theorem mem_piFinset_fin_two {γ : Type*} (s t : Finset γ) (v : Fin 2 → γ) :
    v ∈ Fintype.piFinset ![s, t] ↔ v 0 ∈ s ∧ v 1 ∈ t := by
  simp only [Fintype.mem_piFinset]
  refine ⟨fun h ↦ ⟨h 0, h 1⟩, fun h i ↦ ?_⟩
  fin_cases i
  · exact h.1
  · exact h.2

/-- The inner `tsum` is a finite box sum. -/
theorem inner_five_eq_sum (r : Fin 2 → ℤ) :
    (∑' v : Fin 2 → ℤ, restratifiedFive (splitFive.symm (r, v)) *
        X ^ (HJO.Q 3 5 (splitFive.symm (r, v))).toNat) =
      ∑ v ∈ Fintype.piFinset ![Finset.Icc (0 : ℤ) (r 1), Finset.Icc (0 : ℤ) (r 0)],
        restratifiedFive (splitFive.symm (r, v)) *
          X ^ (HJO.Q 3 5 (splitFive.symm (r, v))).toNat := by
  refine tsum_eq_sum fun v hv ↦ ?_
  have h : ¬(0 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 0 ≤ r 1 ∧ v 1 ≤ r 0) := fun hc ↦
    hv ((mem_piFinset_fin_two _ _ v).mpr
      ⟨Finset.mem_Icc.mpr ⟨hc.1, hc.2.2.1⟩, Finset.mem_Icc.mpr ⟨hc.2.1, hc.2.2.2⟩⟩)
  rw [restratifiedFive_split_eq_zero r v h, zero_mul]

/-- The termwise identity inside the box. -/
theorem restratifiedFive_split_of_mem (w : Fin 2 → ℕ) (v : Fin 2 → ℤ)
    (h0 : 0 ≤ v 0) (h1 : 0 ≤ v 1) :
    restratifiedFive (splitFive.symm ((fun j ↦ (w j : ℤ)), v)) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) *
        qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
        (qChoose (X : ℤ⟦X⟧) (w 1) (v 0).toNat * qChoose (X : ℤ⟦X⟧) (w 0) (v 1).toNat) := by
  simp only [restratifiedFive, splitFive_symm_gap_one, splitFive_symm_gap_two,
    splitFive_symm_gap_four, splitFive_symm_gap_seven,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 0 : ℤ) from by positivity)
      (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity),
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity) h0,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 0 : ℤ) from by positivity) h1,
    Int.toNat_natCast]

/--
The `ℤ → ℕ` reindex of the box, coordinatewise as at `b = 4` but with the two radii distinct.
-/
theorem inner_five_reindex (w : Fin 2 → ℕ) :
    (∑ v ∈ Fintype.piFinset ![Finset.Icc (0 : ℤ) (w 1 : ℤ), Finset.Icc (0 : ℤ) (w 0 : ℤ)],
        restratifiedFive (splitFive.symm ((fun j ↦ (w j : ℤ)), v)) *
          X ^ (HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
      ∑ u ∈ Fintype.piFinset ![Finset.range (w 1 + 1), Finset.range (w 0 + 1)],
        restratifiedFive (splitFive.symm ((fun j ↦ (w j : ℤ)), fun j ↦ (u j : ℤ))) *
          X ^ (HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)),
            fun j ↦ (u j : ℤ)))).toNat := by
  refine Finset.sum_nbij'
    (i := fun v : Fin 2 → ℤ ↦ fun j ↦ (v j).toNat)
    (j := fun u : Fin 2 → ℕ ↦ fun j ↦ (u j : ℤ)) ?hi ?hj ?left ?right ?h
  · intro v hv
    obtain ⟨h0, h1⟩ := (mem_piFinset_fin_two _ _ v).mp hv
    rw [Finset.mem_Icc] at h0 h1
    exact (mem_piFinset_fin_two _ _ _).mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  · intro u hu
    obtain ⟨h0, h1⟩ := (mem_piFinset_fin_two _ _ u).mp hu
    rw [Finset.mem_range] at h0 h1
    exact (mem_piFinset_fin_two _ _ _).mpr
      ⟨Finset.mem_Icc.mpr ⟨by positivity, by omega⟩,
       Finset.mem_Icc.mpr ⟨by positivity, by omega⟩⟩
  · intro v hv
    obtain ⟨h0, h1⟩ := (mem_piFinset_fin_two _ _ v).mp hv
    rw [Finset.mem_Icc] at h0 h1
    exact funext fun i ↦ by fin_cases i <;> [exact Int.toNat_of_nonneg h0.1;
      exact Int.toNat_of_nonneg h1.1]
  · intro u _
    funext i
    simp
  · intro v hv
    obtain ⟨h0, h1⟩ := (mem_piFinset_fin_two _ _ v).mp hv
    rw [Finset.mem_Icc] at h0 h1
    have hv' : (fun j ↦ (((v j).toNat : ℕ) : ℤ)) = v :=
      funext fun i ↦ by fin_cases i <;> [exact Int.toNat_of_nonneg h0.1;
        exact Int.toNat_of_nonneg h1.1]
    rw [hv']

/-- The inner sum, factored. -/
theorem inner_five_factored (w : Fin 2 → ℕ) :
    (∑' v : Fin 2 → ℤ, restratifiedFive (splitFive.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
        ∑ u ∈ Fintype.piFinset ![Finset.range (w 1 + 1), Finset.range (w 0 + 1)],
          qChoose (X : ℤ⟦X⟧) (w 1) (u 0) * qChoose (X : ℤ⟦X⟧) (w 0) (u 1) *
            X ^ (HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)),
              fun j ↦ (u j : ℤ)))).toNat := by
  rw [inner_five_eq_sum, inner_five_reindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [restratifiedFive_split_of_mem w (fun j ↦ (u j : ℤ)) (by positivity) (by positivity)]
  simp only [Int.toNat_natCast]
  ring

/-- The box sum as a double sum, with the exponent computed. -/
theorem inner_five_double (w : Fin 2 → ℕ) :
    (∑ u ∈ Fintype.piFinset ![Finset.range (w 1 + 1), Finset.range (w 0 + 1)],
        qChoose (X : ℤ⟦X⟧) (w 1) (u 0) * qChoose (X : ℤ⟦X⟧) (w 0) (u 1) *
          X ^ (HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)),
            fun j ↦ (u j : ℤ)))).toNat) =
      ∑ n₂ ∈ Finset.range (w 0 + 1), ∑ n₁ ∈ Finset.range (w 1 + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + (w 0 : ℤ) ^ 2 + (w 1 : ℤ) ^ 2 +
            n₁ * n₂ - n₁ * (w 0 : ℤ) + n₂ * (w 1 : ℤ) - n₂ * (w 0 : ℤ))).toNat *
          qChoose (X : ℤ⟦X⟧) (w 1) n₁ * qChoose (X : ℤ⟦X⟧) (w 0) n₂ := by
  rw [sum_piFinset_fin_two, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_congr rfl fun n₁ _ ↦ ?_
  have hQ : HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)),
      fun j ↦ ((![n₁, n₂] j : ℕ) : ℤ))) =
      (n₁ ^ 2 + n₂ ^ 2 + (w 0 : ℤ) ^ 2 + (w 1 : ℤ) ^ 2 +
        n₁ * n₂ - n₁ * (w 0 : ℤ) + n₂ * (w 1 : ℤ) - n₂ * (w 0 : ℤ)) := by
    rw [SumToSum.ThreeTwo.Q_three_five, splitFive_symm_gap_one, splitFive_symm_gap_two,
      splitFive_symm_gap_four, splitFive_symm_gap_seven]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [hQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/--
On an antitone tuple the `ℤ⟦X⟧` double sum is the image of `five_iff`'s left side, and `five`
identifies that with the right side, which `rhs_five` turns back into the finsum over `m`.
-/
theorem inner_five_transport (w : Fin 2 → ℕ) (hw : w 1 ≤ w 0) :
    (∑ n₂ ∈ Finset.range (w 0 + 1), ∑ n₁ ∈ Finset.range (w 1 + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + (w 0 : ℤ) ^ 2 + (w 1 : ℤ) ^ 2 +
            n₁ * n₂ - n₁ * (w 0 : ℤ) + n₂ * (w 1 : ℤ) - n₂ * (w 0 : ℤ))).toNat *
          qChoose (X : ℤ⟦X⟧) (w 1) n₁ * qChoose (X : ℤ⟦X⟧) (w 0) n₂) =
      toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 1 w m) := by
  have h1 : w = ![w 0, w 1] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, SumToSum.ThreeTwo.rhs_five hw,
    ← (SumToSum.ThreeTwo.five_iff hw).mp (SumToSum.ThreeTwo.five hw)]
  simp only [map_sum, map_mul, map_pow, toSeries_X, toSeries_qChoose,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

end HJOA3
