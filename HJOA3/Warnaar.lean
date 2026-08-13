module

public import HJOA3.Bridge
public import HJOA3.Fibration
public import HJOA3.Reduction

/-!
# The Warnaar hypothesis, in this project's own vocabulary
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/-- §9's outer `r`-sum against `P_{3,4}`. -/
def OuterChargeFour : Prop :=
  ∑' r : ℕ, HJO.extendedSelfQPochhammerInv r *
      toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 1 (fun _ ↦ r) m) =
    HJO.charge 3 4

/-- The inner sum of `zNat_four_outer`, over `Fin 2 → ℤ`, is `1/(q)_{r₁}` times `S(r₁)`. -/
def InnerFour : Prop :=
  ∀ n : ℕ, (∑' v : Fin 2 → ℤ, restratifiedFour (splitFour.symm ((n : ℤ), v)) *
      X ^ (HJO.Q 3 4 (splitFour.symm ((n : ℤ), v))).toNat) =
    HJO.extendedSelfQPochhammerInv n *
      toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 1 (fun _ ↦ n) m)

/-- `InnerFour` and `OuterChargeFour` imply the HJO conjecture for `(a, b) = (3, 4)`. -/
theorem conjecture_three_four (hi : InnerFour) (hw : OuterChargeFour) : HJO.Conjecture 3 4 := by
  refine conjecture_three_of_conjecture' ?_
  change HJO.zNat 3 4 = HJO.charge 3 4
  rw [zNat_four_outer, tsum_congr hi]
  exact hw

theorem innerFour : InnerFour := fun n ↦ by
  rw [inner_four_factored, inner_four_double, inner_four_transport]

/-- `thm:main` for `b = 4`, on Warnaar alone. -/
theorem conjecture_three_four_of_outerCharge (hw : OuterChargeFour) : HJO.Conjecture 3 4 :=
  conjecture_three_four innerFour hw

end HJOA3
