module

public import QSeriesLib.NumberTheory.HJO.SumToSum.Small
public import HJOA3.AndrewsGordon
public import HJOA3.Warnaar

/-!
# `OuterChargeFour` from Warnaar's `(1.11)` at `𝐤 = 2`
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3.AndrewsGordon

/--
`ℕ × ℕ ≃ (Fin 1 → ℕ) × (Fin 1 → ℕ)`, the reindexing that turns `(1.11)`'s two `Fin 1`-indexed
binder families at `𝐤 = 2` into the plain pair `(r, m)` the `b = 4` case is written with.
-/
def pairEquiv : ℕ × ℕ ≃ (Fin 1 → ℕ) × (Fin 1 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).symm.prodCongr (Equiv.funUnique (Fin 1) ℕ).symm

theorem extendedSelfQPochhammerInv_natCast (r : ℕ) :
    HJO.extendedSelfQPochhammerInv r = qPochhammerSelfInv r := by
  rw [HJO.extendedSelfQPochhammerInv, qPochhammerSelfInv]
  simp

/-- QSeriesLib's `rhsTerm` at `k = 1` is Warnaar's `(1.11)` summand at `𝐤 = 2`. -/
theorem tsum_plusTerm_fibre (r : ℕ) :
    (∑' m : ℕ, plusTerm 0 (fun _ ↦ r) fun _ ↦ m) =
      HJO.extendedSelfQPochhammerInv r *
        toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 1 (fun _ ↦ r) m) := by
  have hvec : (fun _ : Fin 1 ↦ r) = ![r] := by funext i; fin_cases i; rfl
  rw [extendedSelfQPochhammerInv_natCast]
  conv_rhs => rw [hvec, HJO.SumToSum.ThreeOne.rhs_four]
  rw [tsum_eq_sum (s := range (2 * r + 1)) fun m hm ↦ ?_]
  · simp only [map_sum, map_mul, map_pow, toSeries_X, toSeries_qChoose, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [plusTerm_zero, quadExp]; ring
  · rw [plusTerm_zero, qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (by simpa using hm)]
    ring

/-- The sum side of the `b = 4` link. -/
theorem plusLHS_zero_eq :
    plusLHS 0 = ∑' r : ℕ, HJO.extendedSelfQPochhammerInv r *
      toSeries (∑ᶠ m, HJO.SumToSum.ThreeOne.rhsTerm 1 (fun _ ↦ r) m) := by
  have hs : Summable fun p : ℕ × ℕ ↦ plusTerm 0 (pairEquiv p).1 (pairEquiv p).2 :=
    (summable_plusTerm 0).comp_injective pairEquiv.injective
  rw [plusLHS, ← pairEquiv.tsum_eq fun p ↦ plusTerm 0 p.1 p.2, hs.tsum_prod]
  exact tsum_congr fun r ↦ tsum_plusTerm_fibre r

/-- The product side of the `b = 4` link, isolated. -/
def ThetaFour : Prop := plusRHS 0 = HJO.charge 3 4

/-- Warnaar's `(1.11)` at `𝐤 = 2` implies `OuterChargeFour`. -/
theorem outerChargeFour_of_plus (hθ : ThetaFour) (h : Plus 0) : OuterChargeFour := by
  rw [OuterChargeFour, ← plusLHS_zero_eq, show plusLHS 0 = plusRHS 0 from h, show _ = _ from hθ]

/-- `thm:main` for `b = 4`, on Warnaar's own statement. -/
theorem conjecture_three_four_of_warnaar (hθ : ThetaFour) (h : Plus 0) : HJO.Conjecture 3 4 :=
  conjecture_three_four_of_outerCharge (outerChargeFour_of_plus hθ h)

end HJOA3.AndrewsGordon
