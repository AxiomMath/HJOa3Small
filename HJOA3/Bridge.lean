module

public import HJOA3.Pochhammer

/-!
# `ℕ[X]` polynomials as `ℤ⟦X⟧` power series
-/

@[expose] public section

open Polynomial PowerSeries
open scoped QTheory

namespace HJOA3

noncomputable def toSeries : ℕ[X] →+* ℤ⟦X⟧ :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom (Nat.castRingHom ℤ))

@[simp] theorem toSeries_X : toSeries (X : ℕ[X]) = (PowerSeries.X : ℤ⟦X⟧) := by
  simp [toSeries]

@[simp] theorem toSeries_qChoose (n k : ℕ) :
    toSeries (qChoose (X : ℕ[X]) n k) = qChoose (PowerSeries.X : ℤ⟦X⟧) n k := by
  rw [map_qChoose, toSeries_X]

@[simp] theorem toSeries_extendedQChoose (A B : ℤ) :
    toSeries (HJO.SumToSum.extendedQChoose (X : ℕ[X]) A B) =
      HJO.SumToSum.extendedQChoose (PowerSeries.X : ℤ⟦X⟧) A B := by
  rw [HJO.SumToSum.extendedQChoose, HJO.SumToSum.extendedQChoose]
  split_ifs
  · exact toSeries_qChoose _ _
  · exact map_zero _

end HJOA3
