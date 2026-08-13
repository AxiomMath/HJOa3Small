module

public import HJOA3.AndrewsGordon.EightProduct
public import HJOA3.AndrewsGordon.Link
public import HJOA3.EightFromKern

/-!
# `OuterChargeEight` from Warnaar's `(1.10)` at `𝐤 = 3`
-/

@[expose] public section

open Finset Polynomial PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3.AndrewsGordon

/-- Warnaar's `(1.10)` summand at `𝐤 = 3` is §9's outer factor times `thm:sum`'s summand. -/
theorem minusTerm_two_eq (w : Fin 3 → ℕ) (m : Fin 2 → ℕ) (hw : w 2 ≤ w 1) :
    minusTerm 2 w m = HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
      qChoose (X : ℤ⟦X⟧) (w 1) (w 2) * toSeries (SumToSum.ThreeTwo.rhsTerm 2 w m) := by
  have hs1 : ∀ c : ℕ, (Fin.snoc m c : Fin 3 → ℕ) 1 = m 1 := fun c ↦ by simp [Fin.snoc]
  have hs2 : ∀ c : ℕ, (Fin.snoc m c : Fin 3 → ℕ) 2 = c := fun c ↦ by simp [Fin.snoc]
  have harith : w 1 - w 2 + 2 * w 2 = w 2 + w 1 := by omega
  rw [minusTerm, extendedSelfQPochhammerInv_natCast, SumToSum.ThreeTwo.rhsTerm]
  simp [quadExp, Fin.last, Fin.prod_univ_succ, hs1, hs2, harith]
  ring_nf

/-- The fibre of `(1.10)`'s sum at `𝐤 = 3` over one triple of radii. -/
theorem tsum_minusTerm_fibre_two (w : Fin 3 → ℕ) :
    (∑' m : Fin 2 → ℕ, minusTerm 2 w m) =
      HJO.extendedSelfQPochhammerInv (w 0 : ℤ) * qChoose (X : ℤ⟦X⟧) (w 0) (w 1) *
        qChoose (X : ℤ⟦X⟧) (w 1) (w 2) *
        toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 2 w m) := by
  by_cases h₂ : w 2 ≤ w 1
  · by_cases h₁ : w 1 ≤ w 0
    · exact tsum_eq_mul_toSeries_finsum _ _ _ _
        (SumToSum.ThreeTwo.support_rhsTerm_of_antitone 2 w (antitone_of_le₃ w h₁ h₂))
        fun m ↦ minusTerm_two_eq w m h₂
    · have h0 : qChoose (X : ℤ⟦X⟧) (w 0) (w 1) = 0 :=
        qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 0 < w 1 from by omega)
      have hzero : ∀ m : Fin 2 → ℕ, minusTerm 2 w m = 0 := fun m ↦ by
        rw [minusTerm_two_eq w m h₂, h0]; ring
      simp [hzero, h0]
  · have h0 : qChoose (X : ℤ⟦X⟧) (w 1) (w 2) = 0 :=
      qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) (show w 1 < w 2 from by omega)
    have hzero : ∀ m : Fin 2 → ℕ, minusTerm 2 w m = 0 := fun m ↦
      minusTerm_eq_zero_of_lt 2 w m 1 (by simpa using by omega)
    simp [hzero, h0]

/-- The sum side of the `b = 8` link. -/
theorem minusLHS_two_eq :
    minusLHS 2 = ∑' w : Fin 3 → ℕ, HJO.extendedSelfQPochhammerInv (w 0 : ℤ) *
      qChoose (X : ℤ⟦X⟧) (w 0) (w 1) * qChoose (X : ℤ⟦X⟧) (w 1) (w 2) *
      toSeries (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm 2 w m) := by
  rw [minusLHS, (summable_minusTerm 2).tsum_prod]
  exact tsum_congr fun w ↦ tsum_minusTerm_fibre_two w

/-- Warnaar's `(1.10)` at `𝐤 = 3` implies `OuterChargeEight`. -/
theorem outerChargeEight_of_minus (h : Minus 2) : OuterChargeEight := by
  rw [OuterChargeEight, ← minusLHS_two_eq, show minusLHS 2 = minusRHS 2 from h,
    minusRHS_two_eq_charge]

/-- `thm:main` for `b = 8`, on Warnaar's own statement. -/
theorem conjecture_three_eight_of_warnaar (h : Minus 2) : HJO.Conjecture 3 8 :=
  conjecture_three_eight_of_outerCharge (outerChargeEight_of_minus h)

end HJOA3.AndrewsGordon
