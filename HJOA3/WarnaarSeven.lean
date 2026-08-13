module

public import HJOA3.FibrationSeven
public import HJOA3.Warnaar

/-!
# The Warnaar hypothesis at `b = 7`, and `thm:main` for `b = 7`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/-- §9's outer `r`-sum against `P_{3,7}`. -/
def OuterChargeSeven : Prop :=
  ∑' w : Fin 2 → ℕ, HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
      toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 2 w m) =
    HJO.charge 3 7

def InnerSeven : Prop :=
  ∀ w : Fin 2 → ℕ, (∑' v : Fin 4 → ℤ,
      restratifiedSeven (splitSeven.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 7 (splitSeven.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
    HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
      toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 2 w m)

theorem innerSeven : InnerSeven := fun w ↦ by
  rw [inner_seven_factored]
  by_cases hw : w 1 ≤ w 0
  · rw [inner_seven_quad, inner_seven_transport w hw]
  · rw [qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 0 < w 1 from by omega)]
    ring

/-- `InnerSeven` and `OuterChargeSeven` imply the HJO conjecture for `(a, b) = (3, 7)`. -/
theorem conjecture_three_seven (hi : InnerSeven) (hw : OuterChargeSeven) : HJO.Conjecture 3 7 := by
  refine conjecture_three_of_conjecture' ?_
  change HJO.zNat 3 7 = HJO.charge 3 7
  rw [zNat_seven_outer, tsum_congr hi]
  exact hw

/-- `thm:main` for `b = 7`, on Warnaar alone. -/
theorem conjecture_three_seven_of_outerCharge (hw : OuterChargeSeven) : HJO.Conjecture 3 7 :=
  conjecture_three_seven innerSeven hw

end HJOA3
