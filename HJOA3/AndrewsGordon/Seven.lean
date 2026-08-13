module

public import HJOA3.AndrewsGordon.Link
public import HJOA3.AndrewsGordon.SevenProduct
public import HJOA3.WarnaarSeven

/-!
# `OuterChargeSeven` from Warnaar's `(1.11)` at `𝐤 = 3`
-/

@[expose] public section

open Finset Polynomial PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3.AndrewsGordon

/-- Warnaar's `(1.11)` summand at `𝐤 = 3` is §9's outer factor times `thm:sum`'s summand. -/
theorem plusTerm_one_eq (w m : Fin 2 → ℕ) :
    plusTerm 1 w m = HJO.extendedSelfQPochhammerInv (w 0 : ℤ) *
      qChoose (X : ℤ⟦X⟧) (w 0) (w 1) * toSeries (HJO.SumToSum.ThreeOne.rhsTerm 2 w m) := by
  rw [plusTerm, extendedSelfQPochhammerInv_natCast, HJO.SumToSum.ThreeOne.rhsTerm]
  simp [quadExp, Fin.last, Fin.prod_univ_succ]
  ring

/-- The fibre of `(1.11)`'s sum at `𝐤 = 3` over one pair of radii. -/
theorem tsum_plusTerm_fibre_one (w : Fin 2 → ℕ) :
    (∑' m : Fin 2 → ℕ, plusTerm 1 w m) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
        toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 2 w m) := by
  by_cases hw : w 1 ≤ w 0
  · exact tsum_eq_mul_toSeries_finsum _ _ _ _
      (HJO.SumToSum.ThreeOne.support_rhsTerm_of_antitone 2 w (antitone_of_le w hw))
      fun m ↦ plusTerm_one_eq w m
  · have h0 : qChoose (X : ℤ⟦X⟧) (w 0) (w 1) = 0 :=
      qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 0 < w 1 from by omega)
    have hzero : ∀ m : Fin 2 → ℕ, plusTerm 1 w m = 0 := fun m ↦ by
      rw [plusTerm_one_eq w m, h0]; ring
    simp [hzero, h0]

/-- The sum side of the `b = 7` link. -/
theorem plusLHS_one_eq :
    plusLHS 1 = ∑' w : Fin 2 → ℕ, HJO.extendedSelfQPochhammerInv (w 0 : ℤ) *
      qChoose (X : ℤ⟦X⟧) (w 0) (w 1) * toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 2 w m) := by
  rw [plusLHS, (summable_plusTerm 1).tsum_prod]
  exact tsum_congr fun w ↦ tsum_plusTerm_fibre_one w

/-- Warnaar's `(1.11)` at `𝐤 = 3` implies `OuterChargeSeven`. -/
theorem outerChargeSeven_of_plus (h : Plus 1) : OuterChargeSeven := by
  rw [OuterChargeSeven, ← plusLHS_one_eq, show plusLHS 1 = plusRHS 1 from h, plusRHS_one_eq_charge]

/-- `thm:main` for `b = 7`, on Warnaar's own statement. -/
theorem conjecture_three_seven_of_warnaar (h : Plus 1) : HJO.Conjecture 3 7 :=
  conjecture_three_seven_of_outerCharge (outerChargeSeven_of_plus h)

end HJOA3.AndrewsGordon
