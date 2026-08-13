module

public import HJOA3.FibrationEight
public import HJOA3.Warnaar

/-!
# The Warnaar hypothesis at `b = 8`, and `thm:main` for `b = 8`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/-- §9's outer `r`-sum against `P_{3,8}`. -/
def OuterChargeEight : Prop :=
  ∑' w : Fin 3 → ℕ, HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
      qChoose (X : ℤ⟦X⟧) (w 1) (w 2) *
      toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 2 w m) =
    HJO.charge 3 8

def InnerEight : Prop :=
  ∀ w : Fin 3 → ℕ, (∑' v : Fin 4 → ℤ,
      restratifiedEight (splitEight.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 8 (splitEight.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
    HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
      qChoose (X : ℤ⟦X⟧) (w 1) (w 2) *
      toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 2 w m)

/-- `InnerEight` follows from `thm:sum` at `b = 8` alone. -/
theorem innerEight (he : SumToSumEight) : InnerEight := fun w ↦ by
  rw [inner_eight_factored]
  by_cases h21 : w 1 ≤ w 0
  · by_cases h32 : w 2 ≤ w 1
    · rw [inner_eight_quad, inner_eight_transport he w h21 h32]
    · rw [qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 1 < w 2 from by omega)]
      ring
  · rw [qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 0 < w 1 from by omega)]
    ring

/-- `InnerEight` and `OuterChargeEight` imply the HJO conjecture for `(a, b) = (3, 8)`. -/
theorem conjecture_three_eight (hi : InnerEight) (hw : OuterChargeEight) : HJO.Conjecture 3 8 := by
  refine conjecture_three_of_conjecture' ?_
  change HJO.zNat 3 8 = HJO.charge 3 8
  rw [zNat_eight_outer, tsum_congr hi]
  exact hw

/-- `thm:main` for `b = 8`, on `thm:sum` and Warnaar. -/
theorem conjecture_three_eight_of_sumToSum (he : SumToSumEight) (hw : OuterChargeEight) :
    HJO.Conjecture 3 8 :=
  conjecture_three_eight (innerEight he) hw

end HJOA3
