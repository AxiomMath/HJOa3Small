module

public import HJOA3.AndrewsGordon.FiveProduct
public import HJOA3.AndrewsGordon.Link
public import HJOA3.WarnaarFive

/-!
# `OuterChargeFive` from Warnaar's `(1.10)` at `𝐤 = 2`
-/

@[expose] public section

open Finset Polynomial PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3.AndrewsGordon

/-- Warnaar's `(1.10)` summand at `𝐤 = 2` is §9's outer factor times `thm:sum`'s summand. -/
theorem minusTerm_one_eq (w : Fin 2 → ℕ) (m : Fin 1 → ℕ) (hw : w 1 ≤ w 0) :
    minusTerm 1 w m = HJO.extendedSelfQPochhammerInv (w 0 : ℤ) *
      qChoose (X : ℤ⟦X⟧) (w 0) (w 1) * toSeries (SumToSum.ThreeTwo.rhsTerm 1 w m) := by
  rw [minusTerm_one w m hw, extendedSelfQPochhammerInv_natCast, SumToSum.ThreeTwo.rhsTerm]
  simp [quadExp, Fin.last]
  ring

/-- The fibre of `(1.10)`'s sum at `𝐤 = 2` over one pair of radii. -/
theorem tsum_minusTerm_fibre_one (w : Fin 2 → ℕ) :
    (∑' m : Fin 1 → ℕ, minusTerm 1 w m) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
        toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 1 w m) := by
  by_cases hw : w 1 ≤ w 0
  · exact tsum_eq_mul_toSeries_finsum _ _ _ _
      (SumToSum.ThreeTwo.support_rhsTerm_of_antitone 1 w (antitone_of_le w hw))
      fun m ↦ minusTerm_one_eq w m hw
  · have h0 : qChoose (X : ℤ⟦X⟧) (w 0) (w 1) = 0 :=
      qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 0 < w 1 from by omega)
    have hzero : ∀ m : Fin 1 → ℕ, minusTerm 1 w m = 0 := fun m ↦
      minusTerm_eq_zero_of_lt 1 w m 0 (by simpa using by omega)
    simp [hzero, h0]

/-- The sum side of the `b = 5` link. -/
theorem minusLHS_one_eq :
    minusLHS 1 = ∑' w : Fin 2 → ℕ, HJO.extendedSelfQPochhammerInv (w 0 : ℤ) *
      qChoose (X : ℤ⟦X⟧) (w 0) (w 1) * toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 1 w m) := by
  rw [minusLHS, (summable_minusTerm 1).tsum_prod]
  exact tsum_congr fun w ↦ tsum_minusTerm_fibre_one w

/-- Warnaar's `(1.10)` at `𝐤 = 2` implies `OuterChargeFive`. -/
theorem outerChargeFive_of_minus (h : Minus 1) : OuterChargeFive := by
  rw [OuterChargeFive, ← minusLHS_one_eq, show minusLHS 1 = minusRHS 1 from h,
    minusRHS_one_eq_charge]

/-- `thm:main` for `b = 5`, on Warnaar's own statement. -/
theorem conjecture_three_five_of_warnaar (h : Minus 1) : HJO.Conjecture 3 5 :=
  conjecture_three_five_of_outerCharge (outerChargeFive_of_minus h)

end HJOA3.AndrewsGordon
