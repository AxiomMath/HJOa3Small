module

public import HJOA3.Bridge
public import HJOA3.SumToSum.ThreeOne.Small
public import HJOA3.Reduction
public import HJOA3.SumToSum.Box
public import Mathlib.Data.Int.Interval

/-!
# Fibrations of `HJO.zNat` for `b = 4, 5, 7, 8`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/--
Split `G → ℤ` for `G = {1, 2, 5}` into the pinned coordinate `n₅ = r₁` and the free pair `(n₁,
n₂)`.
-/
def splitFour : ((finspan {3, 4}).gaps → ℤ) ≃ ℤ × (Fin 2 → ℤ) where
  toFun n := (n g%5, ![n g%1, n g%2])
  invFun p := fun i ↦ if i.val = 1 then p.2 0 else if i.val = 2 then p.2 1 else p.1
  left_inv n := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨r, v⟩ := p
    refine Prod.ext rfl (funext fun i ↦ ?_)
    fin_cases i <;> rfl

/-- The fibration of `zNat 3 4` by the pinned coordinate. -/
theorem zNat_four_fibred :
    HJO.zNat 3 4 = ∑' r : ℤ, ∑' v : Fin 2 → ℤ,
      restratifiedFour (splitFour.symm (r, v)) *
        X ^ (HJO.Q 3 4 (splitFour.symm (r, v))).toNat := by
  have hs : Summable fun p : ℤ × (Fin 2 → ℤ) ↦
      restratifiedFour (splitFour.symm p) *
        X ^ (HJO.Q 3 4 (splitFour.symm p)).toNat :=
    summable_restratifiedFour.comp_injective splitFour.symm.injective
  rw [zNat_four, ← splitFour.symm.tsum_eq
      (fun n ↦ restratifiedFour n * X ^ (HJO.Q 3 4 n).toNat),
    hs.tsum_prod]

/--
Split `G → ℤ` for `G = gaps ⟨3, 5⟩` into the `2` pinned coordinates `r₁, …, r_2` (the gaps `7`,
`4`, in that order) and the `2` free ones (the gaps `1`, `2`).
-/
def splitFive : ((finspan {3, 5}).gaps → ℤ) ≃ (Fin 2 → ℤ) × (Fin 2 → ℤ) where
  toFun n := (![n g%7, n g%4], ![n g%1, n g%2])
  invFun p := fun i ↦
    if i.val = 1 then p.2 0 else
    if i.val = 2 then p.2 1 else
    if i.val = 4 then p.1 1 else
    p.1 0
  left_inv n := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨r, v⟩ := p
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> rfl

/-- The fibration of `zNat 3 5` by the pinned coordinates. -/
theorem zNat_five_fibred :
    HJO.zNat 3 5 = ∑' r : Fin 2 → ℤ, ∑' v : Fin 2 → ℤ,
      restratifiedFive (splitFive.symm (r, v)) *
        X ^ (HJO.Q 3 5 (splitFive.symm (r, v))).toNat := by
  have hs : Summable fun p : (Fin 2 → ℤ) × (Fin 2 → ℤ) ↦
      restratifiedFive (splitFive.symm p) *
        X ^ (HJO.Q 3 5 (splitFive.symm p)).toNat :=
    summable_restratifiedFive.comp_injective splitFive.symm.injective
  rw [zNat_five, ← splitFive.symm.tsum_eq
      (fun n ↦ restratifiedFive n * X ^ (HJO.Q 3 5 n).toNat),
    hs.tsum_prod]

/--
Split `G → ℤ` for `G = gaps ⟨3, 7⟩` into the `2` pinned coordinates `r₁, …, r_2` (the gaps
`11`, `8`, in that order) and the `4` free ones (the gaps `1`, `2`, `4`, `5`).
-/
def splitSeven : ((finspan {3, 7}).gaps → ℤ) ≃ (Fin 2 → ℤ) × (Fin 4 → ℤ) where
  toFun n := (![n g%11, n g%8], ![n g%1, n g%2, n g%4, n g%5])
  invFun p := fun i ↦
    if i.val = 1 then p.2 0 else
    if i.val = 2 then p.2 1 else
    if i.val = 4 then p.2 2 else
    if i.val = 5 then p.2 3 else
    if i.val = 8 then p.1 1 else
    p.1 0
  left_inv n := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨r, v⟩ := p
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> rfl

/-- The fibration of `zNat 3 7` by the pinned coordinates. -/
theorem zNat_seven_fibred :
    HJO.zNat 3 7 = ∑' r : Fin 2 → ℤ, ∑' v : Fin 4 → ℤ,
      restratifiedSeven (splitSeven.symm (r, v)) *
        X ^ (HJO.Q 3 7 (splitSeven.symm (r, v))).toNat := by
  have hs : Summable fun p : (Fin 2 → ℤ) × (Fin 4 → ℤ) ↦
      restratifiedSeven (splitSeven.symm p) *
        X ^ (HJO.Q 3 7 (splitSeven.symm p)).toNat :=
    summable_restratifiedSeven.comp_injective splitSeven.symm.injective
  rw [zNat_seven, ← splitSeven.symm.tsum_eq
      (fun n ↦ restratifiedSeven n * X ^ (HJO.Q 3 7 n).toNat),
    hs.tsum_prod]

/--
Split `G → ℤ` for `G = gaps ⟨3, 8⟩` into the `3` pinned coordinates `r₁, …, r_3` (the gaps
`13`, `10`, `7`, in that order) and the `4` free ones (the gaps `1`, `2`, `4`, `5`).
-/
def splitEight : ((finspan {3, 8}).gaps → ℤ) ≃ (Fin 3 → ℤ) × (Fin 4 → ℤ) where
  toFun n := (![n g%13, n g%10, n g%7], ![n g%1, n g%2, n g%4, n g%5])
  invFun p := fun i ↦
    if i.val = 1 then p.2 0 else
    if i.val = 2 then p.2 1 else
    if i.val = 4 then p.2 2 else
    if i.val = 5 then p.2 3 else
    if i.val = 10 then p.1 1 else
    if i.val = 7 then p.1 2 else
    p.1 0
  left_inv n := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨r, v⟩ := p
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> rfl

/-- The fibration of `zNat 3 8` by the pinned coordinates. -/
theorem zNat_eight_fibred :
    HJO.zNat 3 8 = ∑' r : Fin 3 → ℤ, ∑' v : Fin 4 → ℤ,
      restratifiedEight (splitEight.symm (r, v)) *
        X ^ (HJO.Q 3 8 (splitEight.symm (r, v))).toNat := by
  have hs : Summable fun p : (Fin 3 → ℤ) × (Fin 4 → ℤ) ↦
      restratifiedEight (splitEight.symm p) *
        X ^ (HJO.Q 3 8 (splitEight.symm p)).toNat :=
    summable_restratifiedEight.comp_injective splitEight.symm.injective
  rw [zNat_eight, ← splitEight.symm.tsum_eq
      (fun n ↦ restratifiedEight n * X ^ (HJO.Q 3 8 n).toNat),
    hs.tsum_prod]

/-- `restratifiedFour` vanishes off the cone. -/
theorem restratifiedFour_split_eq_zero (r : ℤ) (v : Fin 2 → ℤ)
    (h : ¬(0 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 0 ≤ r ∧ v 1 ≤ r)) :
    restratifiedFour (splitFour.symm (r, v)) = 0 := by
  have e5 : (splitFour.symm (r, v)) g%5 = r := rfl
  have e1 : (splitFour.symm (r, v)) g%1 = v 0 := rfl
  have e2 : (splitFour.symm (r, v)) g%2 = v 1 := rfl
  simp only [restratifiedFour, e5, e1, e2]
  rcases lt_or_ge (v 0) 0 with h1 | h1
  · rw [extendedQChoose_eq_zero (A := r) (B := v 0) (Or.inr h1), mul_zero]
  rcases lt_or_ge (v 1) 0 with h2 | h2
  · rw [extendedQChoose_eq_zero (A := r) (B := v 1) (Or.inr h2)]
    ring
  rcases lt_or_ge r (v 0) with h15 | h15
  · rw [extendedQChoose_eq_zero_of_lt (A := r) (B := v 0) h15, mul_zero]
  rcases lt_or_ge r (v 1) with h25 | h25
  · rw [extendedQChoose_eq_zero_of_lt (A := r) (B := v 1) h25]
    ring
  exact absurd ⟨h1, h2, h15, h25⟩ h

/-- The inner summand of `zNat_four_fibred` is supported in the cone. -/
theorem support_inner_four (r : ℤ) :
    (Function.support fun v : Fin 2 → ℤ ↦ restratifiedFour (splitFour.symm (r, v)) *
        X ^ (HJO.Q 3 4 (splitFour.symm (r, v))).toNat) ⊆
      {v | 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 0 ≤ r ∧ v 1 ≤ r} := by
  intro v hv
  by_contra hc
  exact hv (by simp only [restratifiedFour_split_eq_zero r v hc, zero_mul])

/-- For a negative pinned coordinate the summand vanishes: `1/(q)_{r₁}` is zero there. -/
theorem restratifiedFour_split_eq_zero_of_neg {r : ℤ} (hr : r < 0) (v : Fin 2 → ℤ) :
    restratifiedFour (splitFour.symm (r, v)) = 0 := by
  have e5 : (splitFour.symm (r, v)) g%5 = r := rfl
  simp only [restratifiedFour, e5, extendedSelfQPochhammerInv_of_neg hr]
  ring

/-- The outer sum runs over `ℕ`. -/
theorem zNat_four_outer :
    HJO.zNat 3 4 = ∑' n : ℕ, ∑' v : Fin 2 → ℤ,
      restratifiedFour (splitFour.symm ((n : ℤ), v)) *
        X ^ (HJO.Q 3 4 (splitFour.symm ((n : ℤ), v))).toNat := by
  rw [zNat_four_fibred]
  refine (Function.Injective.tsum_eq (g := fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective ?_).symm
  intro r hr
  rcases lt_or_ge r 0 with h | h
  · refine absurd ?_ hr
    have hz : ∀ v : Fin 2 → ℤ, restratifiedFour (splitFour.symm (r, v)) *
        X ^ (HJO.Q 3 4 (splitFour.symm (r, v))).toNat = 0 :=
      fun v ↦ by rw [restratifiedFour_split_eq_zero_of_neg h v, zero_mul]
    simp only [hz, tsum_zero]
  · exact ⟨r.toNat, Int.toNat_of_nonneg h⟩

/-- The inner `tsum` is a finite box sum. -/
theorem inner_four_eq_sum (r : ℤ) :
    (∑' v : Fin 2 → ℤ, restratifiedFour (splitFour.symm (r, v)) *
        X ^ (HJO.Q 3 4 (splitFour.symm (r, v))).toNat) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin 2 ↦ Finset.Icc (0 : ℤ) r),
        restratifiedFour (splitFour.symm (r, v)) *
          X ^ (HJO.Q 3 4 (splitFour.symm (r, v))).toNat := by
  refine tsum_eq_sum fun v hv ↦ ?_
  have h : ¬(0 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 0 ≤ r ∧ v 1 ≤ r) := by
    intro hc
    refine hv ?_
    simp only [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact Finset.mem_Icc.mpr ⟨hc.1, hc.2.2.1⟩
    · exact Finset.mem_Icc.mpr ⟨hc.2.1, hc.2.2.2⟩
  rw [restratifiedFour_split_eq_zero r v h, zero_mul]

/-- The termwise identity inside the box. -/
theorem restratifiedFour_split_of_mem (n : ℕ) (v : Fin 2 → ℤ)
    (h0 : 0 ≤ v 0) (h1 : 0 ≤ v 1) :
    restratifiedFour (splitFour.symm ((n : ℤ), v)) =
      HJO.extendedSelfQPochhammerInv (n : ℤ) *
        qChoose (X : ℤ⟦X⟧) n (v 1).toNat *
        qChoose (X : ℤ⟦X⟧) n (v 0).toNat := by
  have e5 : (splitFour.symm ((n : ℤ), v)) g%5 = (n : ℤ) := rfl
  have e1 : (splitFour.symm ((n : ℤ), v)) g%1 = v 0 := rfl
  have e2 : (splitFour.symm ((n : ℤ), v)) g%2 = v 1 := rfl
  simp only [restratifiedFour, e5, e1, e2,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (n : ℤ) from by positivity) h1,
    extendedQChoose_of_nonneg (show (0 : ℤ) ≤ (n : ℤ) from by positivity) h0,
    Int.toNat_natCast]

/-- The `ℤ → ℕ` reindex of the box. -/
theorem inner_four_reindex (n : ℕ) :
    (∑ v ∈ Fintype.piFinset (fun _ : Fin 2 ↦ Finset.Icc (0 : ℤ) (n : ℤ)),
        restratifiedFour (splitFour.symm ((n : ℤ), v)) *
          X ^ (HJO.Q 3 4 (splitFour.symm ((n : ℤ), v))).toNat) =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin 2 ↦ Finset.range (n + 1)),
        restratifiedFour (splitFour.symm ((n : ℤ), fun j ↦ (w j : ℤ))) *
          X ^ (HJO.Q 3 4 (splitFour.symm ((n : ℤ), fun j ↦ (w j : ℤ)))).toNat := by
  refine Finset.sum_nbij'
    (i := fun v : Fin 2 → ℤ ↦ fun j ↦ (v j).toNat)
    (j := fun w : Fin 2 → ℕ ↦ fun j ↦ (w j : ℤ)) ?hi ?hj ?left ?right ?h
  · intro v hv
    simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hv
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    exact fun i ↦ by have := hv i; omega
  · intro w hw
    simp only [Fintype.mem_piFinset, Finset.mem_range] at hw
    simp only [Fintype.mem_piFinset, Finset.mem_Icc]
    exact fun i ↦ by have := hw i; omega
  · intro v hv
    simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hv
    exact funext fun i ↦ Int.toNat_of_nonneg (hv i).1
  · intro w _
    funext i
    simp
  · intro v hv
    simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hv
    have hv' : (fun j ↦ (((v j).toNat : ℕ) : ℤ)) = v :=
      funext fun i ↦ Int.toNat_of_nonneg (hv i).1
    rw [hv']

/-- The inner sum, factored. -/
theorem inner_four_factored (n : ℕ) :
    (∑' v : Fin 2 → ℤ, restratifiedFour (splitFour.symm ((n : ℤ), v)) *
        X ^ (HJO.Q 3 4 (splitFour.symm ((n : ℤ), v))).toNat) =
      HJO.extendedSelfQPochhammerInv (n : ℤ) *
        ∑ w ∈ Fintype.piFinset (fun _ : Fin 2 ↦ Finset.range (n + 1)),
          qChoose (X : ℤ⟦X⟧) n (w 1) * qChoose (X : ℤ⟦X⟧) n (w 0) *
            X ^ (HJO.Q 3 4 (splitFour.symm ((n : ℤ), fun j ↦ (w j : ℤ)))).toNat := by
  rw [inner_four_eq_sum, inner_four_reindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [restratifiedFour_split_of_mem n (fun j ↦ (w j : ℤ))
    (by positivity) (by positivity)]
  simp only [Int.toNat_natCast]
  ring

/-- The box sum as a double sum, with the exponent computed. -/
theorem inner_four_double (n : ℕ) :
    (∑ w ∈ Fintype.piFinset (fun _ : Fin 2 ↦ Finset.range (n + 1)),
        qChoose (X : ℤ⟦X⟧) n (w 1) * qChoose (X : ℤ⟦X⟧) n (w 0) *
          X ^ (HJO.Q 3 4 (splitFour.symm ((n : ℤ), fun j ↦ (w j : ℤ)))).toNat) =
      ∑ n₁ ∈ Finset.range (n + 1), ∑ n₂ ∈ Finset.range (n + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + n ^ 2 + n₁ * n₂ - n₁ * n : ℤ)).toNat *
          qChoose (X : ℤ⟦X⟧) n n₁ * qChoose (X : ℤ⟦X⟧) n n₂ := by
  rw [sum_piFinset_fin_two]
  refine Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₂ _ ↦ ?_
  have e1 : (splitFour.symm ((n : ℤ), fun j ↦ ((![n₁, n₂] j : ℕ) : ℤ))) g%1 = (n₁ : ℤ) := rfl
  have e2 : (splitFour.symm ((n : ℤ), fun j ↦ ((![n₁, n₂] j : ℕ) : ℤ))) g%2 = (n₂ : ℤ) := rfl
  have e5 : (splitFour.symm ((n : ℤ), fun j ↦ ((![n₁, n₂] j : ℕ) : ℤ))) g%5 = (n : ℤ) := rfl
  have hQ : HJO.Q 3 4 (splitFour.symm ((n : ℤ), fun j ↦ ((![n₁, n₂] j : ℕ) : ℤ))) =
      (n₁ ^ 2 + n₂ ^ 2 + n ^ 2 + n₁ * n₂ - n₁ * n : ℤ) := by
    rw [HJO.Q_three_four, e1, e2, e5]
  rw [hQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/--
The `ℤ⟦X⟧` double sum is the image of `four_iff`'s left side, and `four` identifies that with
the right side, which `rhs_four` turns back into the finsum over `m`.
-/
theorem inner_four_transport (n : ℕ) :
    (∑ n₁ ∈ Finset.range (n + 1), ∑ n₂ ∈ Finset.range (n + 1),
        X ^ ((n₁ ^ 2 + n₂ ^ 2 + n ^ 2 + n₁ * n₂ - n₁ * n : ℤ)).toNat *
          qChoose (X : ℤ⟦X⟧) n n₁ * qChoose (X : ℤ⟦X⟧) n n₂) =
      toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 1 (fun _ ↦ n) m) := by
  have h1 : (fun _ : Fin 1 ↦ n) = ![n] := by
    funext i
    fin_cases i
    rfl
  rw [h1, HJO.SumToSum.ThreeOne.rhs_four,
    ← (HJO.SumToSum.ThreeOne.four_iff n).mp (SumToSum.ThreeOne.four n)]
  simp only [map_sum, map_mul, map_pow, toSeries_X, toSeries_qChoose]

end HJOA3
