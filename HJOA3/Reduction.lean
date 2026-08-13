module

public import QSeriesLib.NumberTheory.HJO.OfPosDef
public import QSeriesLib.NumberTheory.HJO.PosDef
public meta import QSeriesLib.NumberTheory.NumericalSemigroup.Meta
public import HJOA3.Multiplicand

/-!
# Reducing `thm:main` to `ℤ⟦X⟧`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3

/-- The HJO conjecture for `a = 3` is equivalent to its formulation in `ℤ⟦X⟧`. -/
theorem conjecture_three_iff (b : ℕ) : HJO.Conjecture 3 b ↔ HJO.Conjecture' 3 b :=
  HJO.conjecture_iff_conjecture' 3 b (HJO.posDefOn_Q_three_cone b)

/-- `thm:main`'s four cases, in the form the rest of the development will discharge them. -/
theorem conjecture_three_of_conjecture' {b : ℕ} (h : HJO.Conjecture' 3 b) :
    HJO.Conjecture 3 b :=
  (conjecture_three_iff b).mpr h

theorem zNat_four :
    HJO.zNat 3 4 = ∑' n : (finspan {3, 4}).gaps → ℤ,
      restratifiedFour n * X ^ (HJO.Q 3 4 n).toNat := by
  rw [HJO.zNat, HJO.zNat']
  exact tsum_congr fun n ↦ by rw [prod_multiplicand_four_eq_restratified, HJO.Q'_eq_Q]

theorem zNat_five :
    HJO.zNat 3 5 = ∑' n : (finspan {3, 5}).gaps → ℤ,
      restratifiedFive n * X ^ (HJO.Q 3 5 n).toNat := by
  rw [HJO.zNat, HJO.zNat']
  exact tsum_congr fun n ↦ by rw [prod_multiplicand_five_eq_restratified, HJO.Q'_eq_Q]

theorem zNat_seven :
    HJO.zNat 3 7 = ∑' n : (finspan {3, 7}).gaps → ℤ,
      restratifiedSeven n * X ^ (HJO.Q 3 7 n).toNat := by
  rw [HJO.zNat, HJO.zNat']
  exact tsum_congr fun n ↦ by rw [prod_multiplicand_seven_eq_restratified, HJO.Q'_eq_Q]

theorem zNat_eight :
    HJO.zNat 3 8 = ∑' n : (finspan {3, 8}).gaps → ℤ,
      restratifiedEight n * X ^ (HJO.Q 3 8 n).toNat := by
  rw [HJO.zNat, HJO.zNat']
  exact tsum_congr fun n ↦ by rw [prod_multiplicand_eight_eq_restratified, HJO.Q'_eq_Q]

theorem summable_restratifiedFour :
    Summable fun n : (finspan {3, 4}).gaps → ℤ ↦
      restratifiedFour n * X ^ (HJO.Q 3 4 n).toNat :=
  (HJO.summable_of_posDefOn (finspan {3, 4}).gaps 3 4 rfl
    (HJO.posDefOn_Q_three_cone 4)).congr fun n ↦ by
      rw [prod_multiplicand_four_eq_restratified, HJO.Q'_eq_Q]

theorem summable_restratifiedFive :
    Summable fun n : (finspan {3, 5}).gaps → ℤ ↦
      restratifiedFive n * X ^ (HJO.Q 3 5 n).toNat :=
  (HJO.summable_of_posDefOn (finspan {3, 5}).gaps 3 5 rfl
    (HJO.posDefOn_Q_three_cone 5)).congr fun n ↦ by
      rw [prod_multiplicand_five_eq_restratified, HJO.Q'_eq_Q]

theorem summable_restratifiedSeven :
    Summable fun n : (finspan {3, 7}).gaps → ℤ ↦
      restratifiedSeven n * X ^ (HJO.Q 3 7 n).toNat :=
  (HJO.summable_of_posDefOn (finspan {3, 7}).gaps 3 7 rfl
    (HJO.posDefOn_Q_three_cone 7)).congr fun n ↦ by
      rw [prod_multiplicand_seven_eq_restratified, HJO.Q'_eq_Q]

theorem summable_restratifiedEight :
    Summable fun n : (finspan {3, 8}).gaps → ℤ ↦
      restratifiedEight n * X ^ (HJO.Q 3 8 n).toNat :=
  (HJO.summable_of_posDefOn (finspan {3, 8}).gaps 3 8 rfl
    (HJO.posDefOn_Q_three_cone 8)).congr fun n ↦ by
      rw [prod_multiplicand_eight_eq_restratified, HJO.Q'_eq_Q]

end HJOA3
