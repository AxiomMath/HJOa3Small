module

public import HJOA3.FibrationFive
public import HJOA3.Warnaar

/-!
# The Warnaar hypothesis at `b = 5`, and `thm:main` for `b = 5`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/-- §9's outer `r`-sum against `P_{3,5}`. -/
def OuterChargeFive : Prop :=
  ∑' w : Fin 2 → ℕ, HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
      toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 1 w m) =
    HJO.charge 3 5

def InnerFive : Prop :=
  ∀ w : Fin 2 → ℕ, (∑' v : Fin 2 → ℤ,
      restratifiedFive (splitFive.symm ((fun j ↦ (w j : ℤ)), v)) *
        X ^ (HJO.Q 3 5 (splitFive.symm ((fun j ↦ (w j : ℤ)), v))).toNat) =
    HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
      toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 1 w m)

theorem innerFive : InnerFive := fun w ↦ by
  rw [inner_five_factored]
  by_cases hw : w 1 ≤ w 0
  · rw [inner_five_double, inner_five_transport w hw]
  · rw [qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 0 < w 1 from by omega)]
    ring

/-- `InnerFive` and `OuterChargeFive` imply the HJO conjecture for `(a, b) = (3, 5)`. -/
theorem conjecture_three_five (hi : InnerFive) (hw : OuterChargeFive) : HJO.Conjecture 3 5 := by
  refine conjecture_three_of_conjecture' ?_
  change HJO.zNat 3 5 = HJO.charge 3 5
  rw [zNat_five_outer, tsum_congr hi]
  exact hw

/-- `thm:main` for `b = 5`, on Warnaar alone. -/
theorem conjecture_three_five_of_outerCharge (hw : OuterChargeFive) : HJO.Conjecture 3 5 :=
  conjecture_three_five innerFive hw

end HJOA3
