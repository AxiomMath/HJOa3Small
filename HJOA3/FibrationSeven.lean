module

public import HJOA3.FibrationFive
public import HJOA3.SumToSum.ThreeOne.Seven

/-!
# `thm:main` for `b = 7`: the fibration chain with a four-dimensional free block
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/--
The six coordinates of `splitSeven.symm`, as `rfl` lemmas: the gaps of `⟨3, 7⟩` are `1, 2, 4,
5, 8, 11`, with the first four free and `8, 11` pinned to `r₂, r₁`.
-/
theorem splitSeven_symm_gap_one (r : Fin 2 → ℤ) (v : Fin 4 → ℤ) :
    (splitSeven.symm (r, v)) g%1 = v 0 := rfl

theorem splitSeven_symm_gap_two (r : Fin 2 → ℤ) (v : Fin 4 → ℤ) :
    (splitSeven.symm (r, v)) g%2 = v 1 := rfl

theorem splitSeven_symm_gap_four (r : Fin 2 → ℤ) (v : Fin 4 → ℤ) :
    (splitSeven.symm (r, v)) g%4 = v 2 := rfl

theorem splitSeven_symm_gap_five (r : Fin 2 → ℤ) (v : Fin 4 → ℤ) :
    (splitSeven.symm (r, v)) g%5 = v 3 := rfl

theorem splitSeven_symm_gap_eight (r : Fin 2 → ℤ) (v : Fin 4 → ℤ) :
    (splitSeven.symm (r, v)) g%8 = r 1 := rfl

theorem splitSeven_symm_gap_eleven (r : Fin 2 → ℤ) (v : Fin 4 → ℤ) :
    (splitSeven.symm (r, v)) g%11 = r 0 := rfl

/-- `restratifiedSeven` vanishes off the box. -/
theorem restratifiedSeven_split_eq_zero (r : Fin 2 → ℤ) (v : Fin 4 → ℤ)
    (h : ¬(0 ≤ v 0 ∧ v 0 ≤ r 1 ∧ 0 ≤ v 1 ∧ v 1 ≤ r 1 ∧
      0 ≤ v 2 ∧ v 2 ≤ r 0 ∧ 0 ≤ v 3 ∧ v 3 ≤ r 1)) :
    restratifiedSeven (splitSeven.symm (r, v)) = 0 := by
  simp only [restratifiedSeven, splitSeven_symm_gap_one, splitSeven_symm_gap_two,
    splitSeven_symm_gap_four, splitSeven_symm_gap_five, splitSeven_symm_gap_eight,
    splitSeven_symm_gap_eleven]
  rcases lt_or_ge (v 0) 0 with h0 | h0
  · rw [extendedQChoose_eq_zero (A := r 1) (B := v 0) (Or.inr h0)]
    ring
  rcases lt_or_ge (r 1) (v 0) with h0' | h0'
  · rw [extendedQChoose_eq_zero_of_lt (A := r 1) (B := v 0) h0']
    ring
  rcases lt_or_ge (v 3) 0 with h3 | h3
  · rw [extendedQChoose_eq_zero (A := r 1) (B := v 3) (Or.inr h3)]
    ring
  rcases lt_or_ge (r 1) (v 3) with h3' | h3'
  · rw [extendedQChoose_eq_zero_of_lt (A := r 1) (B := v 3) h3']
    ring
  rcases lt_or_ge (v 1) 0 with h1 | h1
  · rw [extendedQChoose_eq_zero (A := v 3) (B := v 1) (Or.inr h1)]
    ring
  rcases lt_or_ge (r 1) (v 1) with h1' | h1'
  · rw [extendedQChoose_eq_zero_of_lt (A := v 3) (B := v 1) (by omega)]
    ring
  rcases lt_or_ge (v 2) 0 with h2 | h2
  · rw [extendedQChoose_eq_zero (A := r 0 - v 0) (B := v 2 - v 0) (Or.inr (by omega))]
    ring
  rcases lt_or_ge (r 0) (v 2) with h2' | h2'
  · rw [extendedQChoose_eq_zero_of_lt (A := r 0 - v 0) (B := v 2 - v 0) (by omega)]
    ring
  exact absurd ⟨h0, h0', h1, h1', h2, h2', h3, h3'⟩ h

/-- The inner summand of `zNat_seven_fibred` is supported in the box. -/
theorem support_inner_seven (r : Fin 2 → ℤ) :
    (Function.support fun v : Fin 4 → ℤ ↦ restratifiedSeven (splitSeven.symm (r, v)) *
        X ^ (HJO.Q 3 7 (splitSeven.symm (r, v))).toNat) ⊆
      {v | 0 ≤ v 0 ∧ v 0 ≤ r 1 ∧ 0 ≤ v 1 ∧ v 1 ≤ r 1 ∧
        0 ≤ v 2 ∧ v 2 ≤ r 0 ∧ 0 ≤ v 3 ∧ v 3 ≤ r 1} := by
  intro v hv
  by_contra hc
  exact hv (by simp only [restratifiedSeven_split_eq_zero r v hc, zero_mul])

/--
The vanishing that pulls the outer sum back to `ℕ`, identical to `b = 5`: a negative `r₁` kills
`1/(q)_{r₁}`, a negative `r₂` kills `qbinom{r₁}{r₂}`.
-/
theorem restratifiedSeven_split_eq_zero_of_outer {r : Fin 2 → ℤ} (hr : r 0 < 0 ∨ r 1 < 0)
    (v : Fin 4 → ℤ) :
    restratifiedSeven (splitSeven.symm (r, v)) = 0 := by
  simp only [restratifiedSeven, splitSeven_symm_gap_eight, splitSeven_symm_gap_eleven]
  rcases hr with h | h
  · rw [extendedSelfQPochhammerInv_of_neg h]
    ring
  · rw [extendedQChoose_eq_zero (A := r 0) (B := r 1) (Or.inr h)]
    ring

/-- The outer sum runs over `Fin 2 → ℕ`. -/
theorem zNat_seven_outer :
    HJO.zNat 3 7 = ∑' w : Fin 2 → ℕ, ∑' v : Fin 4 → ℤ,
      restratifiedSeven (splitSeven.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)), v))).toNat := by
  rw [zNat_seven_fibred]
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
      have hz : ∀ v : Fin 4 → ℤ, restratifiedSeven (splitSeven.symm (r, v)) *
          X ^ (HJO.Q 3 7 (splitSeven.symm (r, v))).toNat = 0 :=
        fun v ↦ by rw [restratifiedSeven_split_eq_zero_of_outer hneg v, zero_mul]
      simp only [hz, tsum_zero]

theorem mem_piFinset_fin_four {γ : Type*} (s t u w : Finset γ) (v : Fin 4 → γ) :
    v ∈ Fintype.piFinset ![s, t, u, w] ↔ v 0 ∈ s ∧ v 1 ∈ t ∧ v 2 ∈ u ∧ v 3 ∈ w := by
  simp only [Fintype.mem_piFinset]
  refine ⟨fun h ↦ ⟨h 0, h 1, h 2, h 3⟩, fun h i ↦ ?_⟩
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/--
The inner `tsum` is a finite box sum, over `[0, r₂] × [0, r₂] × [0, r₁] × [0, r₂]` — the bounds
of `seven_iff`, in `splitSeven`'s coordinate order `n₁, n₂, n₄, n₅`.
-/
theorem inner_seven_eq_sum (r : Fin 2 → ℤ) :
    (∑' v : Fin 4 → ℤ, restratifiedSeven (splitSeven.symm (r, v)) *
        X ^ (HJO.Q 3 7 (splitSeven.symm (r, v))).toNat) =
      ∑ v ∈ Fintype.piFinset ![Finset.Icc (0 : ℤ) (r 1), Finset.Icc (0 : ℤ) (r 1),
          Finset.Icc (0 : ℤ) (r 0), Finset.Icc (0 : ℤ) (r 1)],
        restratifiedSeven (splitSeven.symm (r, v)) *
          X ^ (HJO.Q 3 7 (splitSeven.symm (r, v))).toNat := by
  refine tsum_eq_sum fun v hv ↦ ?_
  have h : ¬(0 ≤ v 0 ∧ v 0 ≤ r 1 ∧ 0 ≤ v 1 ∧ v 1 ≤ r 1 ∧
      0 ≤ v 2 ∧ v 2 ≤ r 0 ∧ 0 ≤ v 3 ∧ v 3 ≤ r 1) := fun hc ↦
    hv ((mem_piFinset_fin_four _ _ _ _ v).mpr
      ⟨Finset.mem_Icc.mpr ⟨hc.1, hc.2.1⟩, Finset.mem_Icc.mpr ⟨hc.2.2.1, hc.2.2.2.1⟩,
       Finset.mem_Icc.mpr ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1⟩,
       Finset.mem_Icc.mpr ⟨hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2⟩⟩)
  rw [restratifiedSeven_split_eq_zero r v h, zero_mul]

/-- The termwise identity inside the box. -/
theorem restratifiedSeven_split_of_mem (w : Fin 2 → ℕ) (v : Fin 4 → ℤ)
    (h0 : 0 ≤ v 0) (h1 : 0 ≤ v 1) (h3 : 0 ≤ v 3) :
    restratifiedSeven (splitSeven.symm ((fun j ↦ (w j : ℤ)), v)) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
        (qChoose (X : ℤ⟦X⟧) (v 3).toNat (v 1).toNat *
          qChoose (X : ℤ⟦X⟧) (w 1) (v 3).toNat *
          qChoose (X : ℤ⟦X⟧) (w 1) (v 0).toNat *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - v 0) (v 2 - v 0)) := by
  simp only [restratifiedSeven, splitSeven_symm_gap_one, splitSeven_symm_gap_two,
    splitSeven_symm_gap_four, splitSeven_symm_gap_five, splitSeven_symm_gap_eight,
    splitSeven_symm_gap_eleven,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 0 : ℤ) from by positivity)
      (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity),
    extendedQChoose_of_nonneg h3 h1,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity) h3,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (w 1 : ℤ) from by positivity) h0,
    Int.toNat_natCast]

/-- The `ℤ → ℕ` reindex of the box, coordinatewise over four coordinates. -/
theorem inner_seven_reindex (w : Fin 2 → ℕ) :
    (∑ v ∈ Fintype.piFinset ![Finset.Icc (0 : ℤ) (w 1 : ℤ), Finset.Icc (0 : ℤ) (w 1 : ℤ),
          Finset.Icc (0 : ℤ) (w 0 : ℤ), Finset.Icc (0 : ℤ) (w 1 : ℤ)],
        restratifiedSeven (splitSeven.symm ((fun j ↦ (w j : ℤ)), v)) *
          X ^ (HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
      ∑ u ∈ Fintype.piFinset ![Finset.range (w 1 + 1), Finset.range (w 1 + 1),
          Finset.range (w 0 + 1), Finset.range (w 1 + 1)],
        restratifiedSeven (splitSeven.symm ((fun j ↦ (w j : ℤ)), fun j ↦ (u j : ℤ))) *
          X ^ (HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)),
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
theorem inner_seven_factored (w : Fin 2 → ℕ) :
    (∑' v : Fin 4 → ℤ, restratifiedSeven (splitSeven.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
        ∑ u ∈ Fintype.piFinset ![Finset.range (w 1 + 1), Finset.range (w 1 + 1),
            Finset.range (w 0 + 1), Finset.range (w 1 + 1)],
          qChoose (X : ℤ⟦X⟧) (u 3) (u 1) * qChoose (X : ℤ⟦X⟧) (w 1) (u 3) *
            qChoose (X : ℤ⟦X⟧) (w 1) (u 0) *
            HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - (u 0 : ℤ))
              ((u 2 : ℤ) - (u 0 : ℤ)) *
            X ^ (HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)),
              fun j ↦ (u j : ℤ)))).toNat := by
  rw [inner_seven_eq_sum, inner_seven_reindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [restratifiedSeven_split_of_mem w (fun j ↦ (u j : ℤ))
    (by positivity) (by positivity) (by positivity)]
  simp only [Int.toNat_natCast]
  ring

/-- The box sum as a quadruple sum, in `seven_iff`'s summation order. -/
theorem inner_seven_quad (w : Fin 2 → ℕ) :
    (∑ u ∈ Fintype.piFinset ![Finset.range (w 1 + 1), Finset.range (w 1 + 1),
          Finset.range (w 0 + 1), Finset.range (w 1 + 1)],
        qChoose (X : ℤ⟦X⟧) (u 3) (u 1) * qChoose (X : ℤ⟦X⟧) (w 1) (u 3) *
          qChoose (X : ℤ⟦X⟧) (w 1) (u 0) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - (u 0 : ℤ))
            ((u 2 : ℤ) - (u 0 : ℤ)) *
          X ^ (HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)),
            fun j ↦ (u j : ℤ)))).toNat) =
      ∑ n₁ ∈ Finset.range (w 1 + 1), ∑ n₄ ∈ Finset.range (w 0 + 1),
      ∑ n₂ ∈ Finset.range (w 1 + 1), ∑ n₅ ∈ Finset.range (w 1 + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + (w 1 : ℤ) ^ 2 + (w 0 : ℤ) ^ 2 +
            n₁ * n₂ - n₁ * (w 1 : ℤ) + n₂ * n₄ + n₄ * n₅ - n₄ * (w 0 : ℤ) -
            n₂ * (w 0 : ℤ))).toNat *
          qChoose (X : ℤ⟦X⟧) n₅ n₂ * qChoose (X : ℤ⟦X⟧) (w 1) n₅ *
          qChoose (X : ℤ⟦X⟧) (w 1) n₁ *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - n₁) ((n₄ : ℤ) - n₁) := by
  rw [sum_piFinset_fin_four, Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_comm]
  refine Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₄ _ ↦
    Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_congr rfl fun n₅ _ ↦ ?_
  have hQ : HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)),
      fun j ↦ ((![n₁, n₂, n₄, n₅] j : ℕ) : ℤ))) =
      (n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + (w 1 : ℤ) ^ 2 + (w 0 : ℤ) ^ 2 +
        n₁ * n₂ - n₁ * (w 1 : ℤ) + n₂ * n₄ + n₄ * n₅ - n₄ * (w 0 : ℤ) - n₂ * (w 0 : ℤ)) := by
    rw [HJO.Q_three_seven, splitSeven_symm_gap_one, splitSeven_symm_gap_two,
      splitSeven_symm_gap_four, splitSeven_symm_gap_five, splitSeven_symm_gap_eight,
      splitSeven_symm_gap_eleven]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/--
On an antitone tuple the `ℤ⟦X⟧` quadruple sum is the image of `seven_iff`'s left side, and
`seven` identifies it with the right side, which `rhs_seven` turns back into the finsum over
`m`.
-/
theorem inner_seven_transport (w : Fin 2 → ℕ) (hw : w 1 ≤ w 0) :
    (∑ n₁ ∈ Finset.range (w 1 + 1), ∑ n₄ ∈ Finset.range (w 0 + 1),
      ∑ n₂ ∈ Finset.range (w 1 + 1), ∑ n₅ ∈ Finset.range (w 1 + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + (w 1 : ℤ) ^ 2 + (w 0 : ℤ) ^ 2 +
            n₁ * n₂ - n₁ * (w 1 : ℤ) + n₂ * n₄ + n₄ * n₅ - n₄ * (w 0 : ℤ) -
            n₂ * (w 0 : ℤ))).toNat *
          qChoose (X : ℤ⟦X⟧) n₅ n₂ * qChoose (X : ℤ⟦X⟧) (w 1) n₅ *
          qChoose (X : ℤ⟦X⟧) (w 1) n₁ *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) ((w 0 : ℤ) - n₁) ((n₄ : ℤ) - n₁)) =
      toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 2 w m) := by
  have h1 : w = ![w 0, w 1] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, HJO.SumToSum.ThreeOne.rhs_seven hw,
    ← (HJO.SumToSum.ThreeOne.seven_iff (w 0) (w 1) hw).mp (SumToSum.ThreeOne.seven hw)]
  simp only [map_sum, map_mul, map_pow, toSeries_X, toSeries_qChoose,
    toSeries_extendedQChoose, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

end HJOA3
