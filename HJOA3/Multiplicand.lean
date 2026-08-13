module

public import QSeriesLib.NumberTheory.HJO.Basic
public meta import QSeriesLib.NumberTheory.NumericalSemigroup.Meta
public import HJOA3.Pochhammer

/-!
# Pointwise restratification for `b = 4, 5, 7, 8`
-/

@[expose] public section

open Finset PowerSeries NumericalSemigroup
open scoped QTheory

namespace HJOA3

/-- A `q`-binomial coefficient as an explicit Pochhammer product. -/
theorem extendedQChoose_eq {A B : ℤ} (hB : 0 ≤ B) (hBA : B ≤ A) :
    HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B =
      HJO.extendedSelfQPochhammer A * HJO.extendedSelfQPochhammerInv B *
        HJO.extendedSelfQPochhammerInv (A - B) := by
  have h := extendedQChoose_mul_pochhammer_mul_pochhammer hB hBA
  calc HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B
      = HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B *
          (HJO.extendedSelfQPochhammer B * HJO.extendedSelfQPochhammerInv B) *
          (HJO.extendedSelfQPochhammer (A - B) *
            HJO.extendedSelfQPochhammerInv (A - B)) := by
        rw [extendedSelfQPochhammer_mul_inv hB,
          extendedSelfQPochhammer_mul_inv (show (0 : ℤ) ≤ A - B from by omega)]
        ring
    _ = HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B * HJO.extendedSelfQPochhammer B *
          HJO.extendedSelfQPochhammer (A - B) *
          (HJO.extendedSelfQPochhammerInv B * HJO.extendedSelfQPochhammerInv (A - B)) := by
        ring
    _ = _ := by rw [h]; ring

section four

variable (n : (finspan {3, 4}).gaps → ℤ)

/-- The gap set of `⟨3, 4⟩` is `{1, 2, 5}`, enumerated by `ThreeOne.toGaps 1`. -/
theorem prod_multiplicand_four :
    ∏ i : (finspan {3, 4}).gaps, HJO.multiplicand _ 3 4 n i =
      (HJO.extendedSelfQPochhammer (n g%1) * HJO.extendedSelfQPochhammerInv (n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%1)) *
      (HJO.extendedSelfQPochhammer (n g%2) * HJO.extendedSelfQPochhammerInv (n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%2)) *
      (HJO.extendedSelfQPochhammer (n g%5) *
        HJO.extendedSelfQPochhammerInv (n g%5 - n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%5 - n g%1)) := by
  rw [← (ThreeOne.toGaps_bijective 1).prod_comp (HJO.multiplicand _ 3 4 n),
    Fin.prod_univ_three]
  have h0 : HJO.extend n 0 = 0 := dif_neg (zero_notMem_gaps _)
  have h1 : HJO.extend n 1 = n g%1 := dif_pos (by decide)
  have h2 : HJO.extend n 2 = n g%2 := dif_pos (by decide)
  simp only [HJO.multiplicand, show (ThreeOne.toGaps 1 0) = g%1 from rfl,
    show (ThreeOne.toGaps 1 1) = g%2 from rfl, show (ThreeOne.toGaps 1 2) = g%5 from rfl]
  norm_num only [h0, h1, h2, sub_zero]

/-- The pointwise restratification identity for `b = 4`. -/
theorem prod_multiplicand_four_eq (h1 : 0 ≤ n g%1) (h2 : 0 ≤ n g%2)
    (h15 : n g%1 ≤ n g%5) (h25 : n g%2 ≤ n g%5) :
    ∏ i : (finspan {3, 4}).gaps, HJO.multiplicand _ 3 4 n i =
      HJO.extendedSelfQPochhammerInv (n g%5) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%2) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%1) := by
  rw [prod_multiplicand_four, extendedQChoose_eq h2 h25, extendedQChoose_eq h1 h15]
  set A := HJO.extendedSelfQPochhammer (n g%1)
  set a := HJO.extendedSelfQPochhammerInv (n g%1)
  set B := HJO.extendedSelfQPochhammer (n g%2)
  set b := HJO.extendedSelfQPochhammerInv (n g%2)
  set C := HJO.extendedSelfQPochhammer (n g%5)
  set E := HJO.extendedSelfQPochhammerInv (n g%5)
  set c := HJO.extendedSelfQPochhammerInv (n g%5 - n g%2)
  set d := HJO.extendedSelfQPochhammerInv (n g%5 - n g%1)
  have e1 : A * a = 1 := extendedSelfQPochhammer_mul_inv h1
  have e2 : B * b = 1 := extendedSelfQPochhammer_mul_inv h2
  have e5 : E * C = 1 := extendedSelfQPochhammerInv_mul_self (h1.trans h15)
  linear_combination (a * B * b * b * C * c * d) * e1 + (a * b * C * c * d) * e2 -
    (C * a * b * c * d) * e5

/-- The `b = 4` identity, unconditionally. -/
theorem prod_multiplicand_four_eq' (n : (finspan {3, 4}).gaps → ℤ) :
    ∏ i : (finspan {3, 4}).gaps, HJO.multiplicand _ 3 4 n i =
      HJO.extendedSelfQPochhammerInv (n g%5) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%2) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%1) := by
  rcases lt_or_ge (n g%1) 0 with h1 | h1
  · rw [prod_multiplicand_four, extendedSelfQPochhammer_of_neg h1,
      extendedQChoose_eq_zero (Or.inr h1)]
    ring
  rcases lt_or_ge (n g%2) 0 with h2 | h2
  · rw [prod_multiplicand_four, extendedSelfQPochhammer_of_neg h2,
      extendedQChoose_eq_zero (Or.inr h2)]
    ring
  rcases lt_or_ge (n g%5) (n g%1) with h15 | h15
  · rw [prod_multiplicand_four,
      extendedSelfQPochhammerInv_of_neg (show n g%5 - n g%1 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt h15]
    ring
  rcases lt_or_ge (n g%5) (n g%2) with h25 | h25
  · rw [prod_multiplicand_four,
      extendedSelfQPochhammerInv_of_neg (show n g%5 - n g%2 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt h25]
    ring
  exact prod_multiplicand_four_eq n h1 h2 h15 h25

/--
§9's factorization of `zNat`'s multiplicand product at `b = 4`: `1/(q)_{r₁}`, times the
`q`-binomials `∏_{i<k} qbinom rᵢ rᵢ₊₁`, times the left side of the sum-to-sum conjecture.
-/
noncomputable def restratifiedFour (n : (finspan {3, 4}).gaps → ℤ) : ℤ⟦X⟧ :=
      HJO.extendedSelfQPochhammerInv (n g%5) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%2) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%1)

theorem prod_multiplicand_four_eq_restratified (n : (finspan {3, 4}).gaps → ℤ) :
    ∏ i : (finspan {3, 4}).gaps, HJO.multiplicand _ 3 4 n i = restratifiedFour n :=
  prod_multiplicand_four_eq' n

end four

section seven

variable (n : (finspan {3, 7}).gaps → ℤ)

/--
The gap set of `⟨3, 7⟩` is `{1, 2, 4, 5, 8, 11}`, enumerated by `ThreeOne.toGaps 2` in the order
`1, 4, 2, 5, 8, 11`.
-/
theorem prod_multiplicand_seven :
    ∏ i : (finspan {3, 7}).gaps, HJO.multiplicand _ 3 7 n i =
      (HJO.extendedSelfQPochhammer (n g%1) * HJO.extendedSelfQPochhammerInv (n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%1)) *
      (HJO.extendedSelfQPochhammer (n g%4) *
        HJO.extendedSelfQPochhammerInv (n g%4 - n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%4)) *
      (HJO.extendedSelfQPochhammer (n g%2) * HJO.extendedSelfQPochhammerInv (n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%2)) *
      (HJO.extendedSelfQPochhammer (n g%5) *
        HJO.extendedSelfQPochhammerInv (n g%5 - n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%5)) *
      (HJO.extendedSelfQPochhammer (n g%8) *
        HJO.extendedSelfQPochhammerInv (n g%8 - n g%5) *
        HJO.extendedSelfQPochhammerInv (n g%8 - n g%1)) *
      (HJO.extendedSelfQPochhammer (n g%11 - n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%11 - n g%8) *
        HJO.extendedSelfQPochhammerInv (n g%11 - n g%4)) := by
  rw [← (ThreeOne.toGaps_bijective 2).prod_comp (HJO.multiplicand _ 3 7 n),
    Fin.prod_univ_six]
  have h0 : HJO.extend n 0 = 0 := dif_neg (zero_notMem_gaps _)
  have h1 : HJO.extend n 1 = n g%1 := dif_pos (by decide)
  have h2 : HJO.extend n 2 = n g%2 := dif_pos (by decide)
  have h4 : HJO.extend n 4 = n g%4 := dif_pos (by decide)
  have h5 : HJO.extend n 5 = n g%5 := dif_pos (by decide)
  have h8 : HJO.extend n 8 = n g%8 := dif_pos (by decide)
  simp only [HJO.multiplicand, show (ThreeOne.toGaps 2 0) = g%1 from rfl,
    show (ThreeOne.toGaps 2 1) = g%4 from rfl, show (ThreeOne.toGaps 2 2) = g%2 from rfl,
    show (ThreeOne.toGaps 2 3) = g%5 from rfl, show (ThreeOne.toGaps 2 4) = g%8 from rfl,
    show (ThreeOne.toGaps 2 5) = g%11 from rfl]
  norm_num only [h0, h1, h2, h4, h5, h8, sub_zero]

/-- The pointwise restratification identity for `b = 7`. -/
theorem prod_multiplicand_seven_eq (hn1 : 0 ≤ n g%1) (hn2 : 0 ≤ n g%2)
    (h14 : n g%1 ≤ n g%4) (h25 : n g%2 ≤ n g%5) (h58 : n g%5 ≤ n g%8)
    (h811 : n g%8 ≤ n g%11) (h18 : n g%1 ≤ n g%8) (h411 : n g%4 ≤ n g%11) :
    ∏ i : (finspan {3, 7}).gaps, HJO.multiplicand _ 3 7 n i =
      HJO.extendedSelfQPochhammerInv (n g%11) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%11) (n g%8) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%2) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%8) (n g%5) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%8) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%11 - n g%1) (n g%4 - n g%1)) := by
  have hn4 : 0 ≤ n g%4 := hn1.trans h14
  have hn5 : 0 ≤ n g%5 := hn2.trans h25
  have hn8 : 0 ≤ n g%8 := hn1.trans h18
  have hn11 : 0 ≤ n g%11 := hn8.trans h811
  rw [prod_multiplicand_seven, extendedQChoose_eq hn8 h811, extendedQChoose_eq hn2 h25,
    extendedQChoose_eq hn5 h58, extendedQChoose_eq hn1 h18,
    extendedQChoose_eq (show (0 : ℤ) ≤ n g%4 - n g%1 from by omega)
      (show n g%4 - n g%1 ≤ n g%11 - n g%1 from by omega),
    show n g%11 - n g%1 - (n g%4 - n g%1) = n g%11 - n g%4 from by ring]
  set P1 := HJO.extendedSelfQPochhammer (n g%1)
  set I1 := HJO.extendedSelfQPochhammerInv (n g%1)
  set P2 := HJO.extendedSelfQPochhammer (n g%2)
  set I2 := HJO.extendedSelfQPochhammerInv (n g%2)
  set P4 := HJO.extendedSelfQPochhammer (n g%4)
  set I4 := HJO.extendedSelfQPochhammerInv (n g%4)
  set P5 := HJO.extendedSelfQPochhammer (n g%5)
  set I5 := HJO.extendedSelfQPochhammerInv (n g%5)
  set P8 := HJO.extendedSelfQPochhammer (n g%8)
  set I8 := HJO.extendedSelfQPochhammerInv (n g%8)
  set P11 := HJO.extendedSelfQPochhammer (n g%11)
  set I11 := HJO.extendedSelfQPochhammerInv (n g%11)
  set J41 := HJO.extendedSelfQPochhammerInv (n g%4 - n g%1)
  set J52 := HJO.extendedSelfQPochhammerInv (n g%5 - n g%2)
  set J85 := HJO.extendedSelfQPochhammerInv (n g%8 - n g%5)
  set J81 := HJO.extendedSelfQPochhammerInv (n g%8 - n g%1)
  set A := HJO.extendedSelfQPochhammer (n g%11 - n g%1)
  set J118 := HJO.extendedSelfQPochhammerInv (n g%11 - n g%8)
  set J114 := HJO.extendedSelfQPochhammerInv (n g%11 - n g%4)
  have e1 : P1 * I1 = 1 := extendedSelfQPochhammer_mul_inv hn1
  have e2 : P2 * I2 = 1 := extendedSelfQPochhammer_mul_inv hn2
  have e4 : P4 * I4 = 1 := extendedSelfQPochhammer_mul_inv hn4
  have e5 : P5 * I5 = 1 := extendedSelfQPochhammer_mul_inv hn5
  have e8 : P8 * I8 = 1 := extendedSelfQPochhammer_mul_inv hn8
  have e11 : I11 * P11 = 1 := extendedSelfQPochhammerInv_mul_self hn11
  calc P1 * I1 * I1 * (P4 * J41 * I4) * (P2 * I2 * I2) * (P5 * J52 * I5) *
        (P8 * J85 * J81) * (A * J118 * J114)
      = (P1 * I1) * (P2 * I2) * (P4 * I4) * (P5 * I5) *
          (I1 * I2 * J41 * J52 * P8 * J85 * J81 * A * J118 * J114) := by ring
    _ = I1 * I2 * J41 * J52 * P8 * J85 * J81 * A * J118 * J114 := by
        rw [e1, e2, e4, e5]; ring
    _ = (I11 * P11) * (P5 * I5) * (P8 * I8) *
          (I1 * I2 * J41 * J52 * P8 * J85 * J81 * A * J118 * J114) := by
        rw [e11, e5, e8]; ring
    _ = _ := by ring

/-- The `b = 7` identity, unconditionally. -/
theorem prod_multiplicand_seven_eq' (n : (finspan {3, 7}).gaps → ℤ) :
    ∏ i : (finspan {3, 7}).gaps, HJO.multiplicand _ 3 7 n i =
      HJO.extendedSelfQPochhammerInv (n g%11) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%11) (n g%8) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%2) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%8) (n g%5) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%8) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%11 - n g%1) (n g%4 - n g%1)) := by
  rcases lt_or_ge (n g%1) 0 with h | h_1
  · rw [prod_multiplicand_seven, extendedSelfQPochhammer_of_neg h,
      extendedQChoose_eq_zero (A := n g%8) (B := n g%1) (Or.inr h)]
    ring
  rcases lt_or_ge (n g%2) 0 with h | h_2
  · rw [prod_multiplicand_seven, extendedSelfQPochhammer_of_neg h,
      extendedQChoose_eq_zero (A := n g%5) (B := n g%2) (Or.inr h)]
    ring
  rcases lt_or_ge (n g%4) (n g%1) with h | h_3
  · rw [prod_multiplicand_seven,
      extendedSelfQPochhammerInv_of_neg (show n g%4 - n g%1 < 0 from by omega),
      extendedQChoose_eq_zero (A := n g%11 - n g%1) (B := n g%4 - n g%1)
        (Or.inr (show n g%4 - n g%1 < 0 from by omega))]
    ring
  rcases lt_or_ge (n g%5) (n g%2) with h | h_4
  · rw [prod_multiplicand_seven,
      extendedSelfQPochhammerInv_of_neg (show n g%5 - n g%2 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%5) (B := n g%2)
        (show n g%5 < n g%2 from by omega)]
    ring
  rcases lt_or_ge (n g%8) (n g%5) with h | h_5
  · rw [prod_multiplicand_seven,
      extendedSelfQPochhammerInv_of_neg (show n g%8 - n g%5 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%8) (B := n g%5)
        (show n g%8 < n g%5 from by omega)]
    ring
  rcases lt_or_ge (n g%11) (n g%8) with h | h_6
  · rw [prod_multiplicand_seven,
      extendedSelfQPochhammerInv_of_neg (show n g%11 - n g%8 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%11) (B := n g%8)
        (show n g%11 < n g%8 from by omega)]
    ring
  rcases lt_or_ge (n g%8) (n g%1) with h | h_7
  · rw [prod_multiplicand_seven,
      extendedSelfQPochhammerInv_of_neg (show n g%8 - n g%1 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%8) (B := n g%1)
        (show n g%8 < n g%1 from by omega)]
    ring
  rcases lt_or_ge (n g%11) (n g%4) with h | h
  · rw [prod_multiplicand_seven,
      extendedSelfQPochhammerInv_of_neg (show n g%11 - n g%4 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%11 - n g%1) (B := n g%4 - n g%1)
        (show n g%11 - n g%1 < n g%4 - n g%1 from by omega)]
    ring
  exact prod_multiplicand_seven_eq n h_1 h_2 h_3 h_4 h_5 h_6 h_7 h

/--
§9's factorization of `zNat`'s multiplicand product at `b = 7`: `1/(q)_{r₁}`, times the
`q`-binomials `∏_{i<k} qbinom rᵢ rᵢ₊₁`, times the left side of the sum-to-sum conjecture.
-/
noncomputable def restratifiedSeven (n : (finspan {3, 7}).gaps → ℤ) : ℤ⟦X⟧ :=
      HJO.extendedSelfQPochhammerInv (n g%11) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%11) (n g%8) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%5) (n g%2) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%8) (n g%5) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%8) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%11 - n g%1) (n g%4 - n g%1))

theorem prod_multiplicand_seven_eq_restratified (n : (finspan {3, 7}).gaps → ℤ) :
    ∏ i : (finspan {3, 7}).gaps, HJO.multiplicand _ 3 7 n i = restratifiedSeven n :=
  prod_multiplicand_seven_eq' n

end seven

section five

variable (n : (finspan {3, 5}).gaps → ℤ)

/--
The gap set of `⟨3, 5⟩` is `{1, 2, 4, 7}`, enumerated by `ThreeTwo.toGaps 1` as `2, 1, 4, 7`.
-/
theorem prod_multiplicand_five :
    ∏ i : (finspan {3, 5}).gaps, HJO.multiplicand _ 3 5 n i =
      (HJO.extendedSelfQPochhammer (n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%2)) *
      (HJO.extendedSelfQPochhammer (n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%1)) *
      (HJO.extendedSelfQPochhammer (n g%4) *
        HJO.extendedSelfQPochhammerInv (n g%4 - n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%4)) *
      (HJO.extendedSelfQPochhammer (n g%7) *
        HJO.extendedSelfQPochhammerInv (n g%7 - n g%4) *
        HJO.extendedSelfQPochhammerInv (n g%7 - n g%2)) := by
  rw [← (NumericalSemigroup.ThreeTwo.toGaps_bijective 1).prod_comp (HJO.multiplicand _ 3 5 n),
    Fin.prod_univ_four]
  have h0 : HJO.extend n 0 = 0 := dif_neg (zero_notMem_gaps _)
  have h1 : HJO.extend n 1 = n g%1 := dif_pos (by decide)
  have h2 : HJO.extend n 2 = n g%2 := dif_pos (by decide)
  have h4 : HJO.extend n 4 = n g%4 := dif_pos (by decide)
  simp only [HJO.multiplicand,
    show (NumericalSemigroup.ThreeTwo.toGaps 1 0) = g%2 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 1 1) = g%1 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 1 2) = g%4 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 1 3) = g%7 from rfl]
  norm_num only [h0, h1, h2, h4, sub_zero]

/-- The pointwise restratification identity for `b = 5`. -/
theorem prod_multiplicand_five_eq (hn1 : 0 ≤ n g%1) (hn2 : 0 ≤ n g%2)
    (h14 : n g%1 ≤ n g%4) (h47 : n g%4 ≤ n g%7) (h27 : n g%2 ≤ n g%7) :
    ∏ i : (finspan {3, 5}).gaps, HJO.multiplicand _ 3 5 n i =
      HJO.extendedSelfQPochhammerInv (n g%7) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%4) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%4) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%2)) := by
  have hn4 : 0 ≤ n g%4 := hn1.trans h14
  have hn7 : 0 ≤ n g%7 := hn4.trans h47
  rw [prod_multiplicand_five, extendedQChoose_eq hn4 h47, extendedQChoose_eq hn1 h14,
    extendedQChoose_eq hn2 h27]
  set P1 := HJO.extendedSelfQPochhammer (n g%1)
  set I1 := HJO.extendedSelfQPochhammerInv (n g%1)
  set P2 := HJO.extendedSelfQPochhammer (n g%2)
  set I2 := HJO.extendedSelfQPochhammerInv (n g%2)
  set P4 := HJO.extendedSelfQPochhammer (n g%4)
  set I4 := HJO.extendedSelfQPochhammerInv (n g%4)
  set P7 := HJO.extendedSelfQPochhammer (n g%7)
  set I7 := HJO.extendedSelfQPochhammerInv (n g%7)
  set J41 := HJO.extendedSelfQPochhammerInv (n g%4 - n g%1)
  set J74 := HJO.extendedSelfQPochhammerInv (n g%7 - n g%4)
  set J72 := HJO.extendedSelfQPochhammerInv (n g%7 - n g%2)
  have e1 : P1 * I1 = 1 := extendedSelfQPochhammer_mul_inv hn1
  have e2 : P2 * I2 = 1 := extendedSelfQPochhammer_mul_inv hn2
  have e4 : P4 * I4 = 1 := extendedSelfQPochhammer_mul_inv hn4
  have e7 : I7 * P7 = 1 := extendedSelfQPochhammerInv_mul_self hn7
  calc P2 * I2 * I2 * (P1 * I1 * I1) * (P4 * J41 * I4) * (P7 * J74 * J72)
      = (P1 * I1) * (P2 * I2) * (P4 * I4) * (I1 * I2 * J41 * P7 * J74 * J72) := by ring
    _ = I1 * I2 * J41 * P7 * J74 * J72 := by rw [e1, e2, e4]; ring
    _ = (I7 * P7) * (P4 * I4) * (I1 * I2 * J41 * P7 * J74 * J72) := by rw [e7, e4]; ring
    _ = _ := by ring

/-- The `b = 5` identity, unconditionally. -/
theorem prod_multiplicand_five_eq' (n : (finspan {3, 5}).gaps → ℤ) :
    ∏ i : (finspan {3, 5}).gaps, HJO.multiplicand _ 3 5 n i =
      HJO.extendedSelfQPochhammerInv (n g%7) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%4) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%4) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%2)) := by
  rcases lt_or_ge (n g%1) 0 with h | h_1
  · rw [prod_multiplicand_five, extendedSelfQPochhammer_of_neg h,
      extendedQChoose_eq_zero (A := n g%4) (B := n g%1) (Or.inr h)]
    ring
  rcases lt_or_ge (n g%2) 0 with h | h_2
  · rw [prod_multiplicand_five, extendedSelfQPochhammer_of_neg h,
      extendedQChoose_eq_zero (A := n g%7) (B := n g%2) (Or.inr h)]
    ring
  rcases lt_or_ge (n g%4) (n g%1) with h | h_3
  · rw [prod_multiplicand_five,
      extendedSelfQPochhammerInv_of_neg (show n g%4 - n g%1 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%4) (B := n g%1)
        (show n g%4 < n g%1 from by omega)]
    ring
  rcases lt_or_ge (n g%7) (n g%4) with h | h_4
  · rw [prod_multiplicand_five,
      extendedSelfQPochhammerInv_of_neg (show n g%7 - n g%4 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%7) (B := n g%4)
        (show n g%7 < n g%4 from by omega)]
    ring
  rcases lt_or_ge (n g%7) (n g%2) with h | h
  · rw [prod_multiplicand_five,
      extendedSelfQPochhammerInv_of_neg (show n g%7 - n g%2 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%7) (B := n g%2)
        (show n g%7 < n g%2 from by omega)]
    ring
  exact prod_multiplicand_five_eq n h_1 h_2 h_3 h_4 h

/--
§9's factorization of `zNat`'s multiplicand product at `b = 5`: `1/(q)_{r₁}`, times the
`q`-binomials `∏_{i<k} qbinom rᵢ rᵢ₊₁`, times the left side of the sum-to-sum conjecture.
-/
noncomputable def restratifiedFive (n : (finspan {3, 5}).gaps → ℤ) : ℤ⟦X⟧ :=
      HJO.extendedSelfQPochhammerInv (n g%7) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%4) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%4) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%2))

theorem prod_multiplicand_five_eq_restratified (n : (finspan {3, 5}).gaps → ℤ) :
    ∏ i : (finspan {3, 5}).gaps, HJO.multiplicand _ 3 5 n i = restratifiedFive n :=
  prod_multiplicand_five_eq' n

end five

section eight

variable (n : (finspan {3, 8}).gaps → ℤ)

/--
The gap set of `⟨3, 8⟩` is `{1, 2, 4, 5, 7, 10, 13}`, enumerated by `ThreeTwo.toGaps 2` as `2,
5, 1, 4, 7, 10, 13`.
-/
theorem prod_multiplicand_eight :
    ∏ i : (finspan {3, 8}).gaps, HJO.multiplicand _ 3 8 n i =
      (HJO.extendedSelfQPochhammer (n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%2)) *
      (HJO.extendedSelfQPochhammer (n g%5) *
        HJO.extendedSelfQPochhammerInv (n g%5 - n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%5)) *
      (HJO.extendedSelfQPochhammer (n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%1)) *
      (HJO.extendedSelfQPochhammer (n g%4) *
        HJO.extendedSelfQPochhammerInv (n g%4 - n g%1) *
        HJO.extendedSelfQPochhammerInv (n g%4)) *
      (HJO.extendedSelfQPochhammer (n g%7) *
        HJO.extendedSelfQPochhammerInv (n g%7 - n g%4) *
        HJO.extendedSelfQPochhammerInv (n g%7)) *
      (HJO.extendedSelfQPochhammer (n g%10) *
        HJO.extendedSelfQPochhammerInv (n g%10 - n g%7) *
        HJO.extendedSelfQPochhammerInv (n g%10 - n g%2)) *
      (HJO.extendedSelfQPochhammer (n g%13 - n g%2) *
        HJO.extendedSelfQPochhammerInv (n g%13 - n g%10) *
        HJO.extendedSelfQPochhammerInv (n g%13 - n g%5)) := by
  rw [← (NumericalSemigroup.ThreeTwo.toGaps_bijective 2).prod_comp (HJO.multiplicand _ 3 8 n),
    Fin.prod_univ_seven]
  have h0 : HJO.extend n 0 = 0 := dif_neg (zero_notMem_gaps _)
  have h1 : HJO.extend n 1 = n g%1 := dif_pos (by decide)
  have h2 : HJO.extend n 2 = n g%2 := dif_pos (by decide)
  have h4 : HJO.extend n 4 = n g%4 := dif_pos (by decide)
  have h5 : HJO.extend n 5 = n g%5 := dif_pos (by decide)
  have h7 : HJO.extend n 7 = n g%7 := dif_pos (by decide)
  have h10 : HJO.extend n 10 = n g%10 := dif_pos (by decide)
  simp only [HJO.multiplicand,
    show (NumericalSemigroup.ThreeTwo.toGaps 2 0) = g%2 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 2 1) = g%5 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 2 2) = g%1 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 2 3) = g%4 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 2 4) = g%7 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 2 5) = g%10 from rfl,
    show (NumericalSemigroup.ThreeTwo.toGaps 2 6) = g%13 from rfl]
  norm_num only [h0, h1, h2, h4, h5, h7, h10, sub_zero]

/-- The pointwise restratification identity for `b = 8`. -/
theorem prod_multiplicand_eight_eq (hn1 : 0 ≤ n g%1) (hn2 : 0 ≤ n g%2)
    (h14 : n g%1 ≤ n g%4) (h25 : n g%2 ≤ n g%5) (h47 : n g%4 ≤ n g%7)
    (h710 : n g%7 ≤ n g%10) (h1013 : n g%10 ≤ n g%13) (h210 : n g%2 ≤ n g%10)
    (h513 : n g%5 ≤ n g%13) :
    ∏ i : (finspan {3, 8}).gaps, HJO.multiplicand _ 3 8 n i =
      HJO.extendedSelfQPochhammerInv (n g%13) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%13) (n g%10) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%10) (n g%7) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%4) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%4) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%10) (n g%2) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%13 - n g%2) (n g%5 - n g%2)) := by
  have hn4 : 0 ≤ n g%4 := hn1.trans h14
  have hn5 : 0 ≤ n g%5 := hn2.trans h25
  have hn7 : 0 ≤ n g%7 := hn4.trans h47
  have hn10 : 0 ≤ n g%10 := hn7.trans h710
  have hn13 : 0 ≤ n g%13 := hn10.trans h1013
  rw [prod_multiplicand_eight, extendedQChoose_eq hn10 h1013, extendedQChoose_eq hn7 h710,
    extendedQChoose_eq hn1 h14, extendedQChoose_eq hn4 h47, extendedQChoose_eq hn2 h210,
    extendedQChoose_eq (show (0 : ℤ) ≤ n g%5 - n g%2 from by omega)
      (show n g%5 - n g%2 ≤ n g%13 - n g%2 from by omega),
    show n g%13 - n g%2 - (n g%5 - n g%2) = n g%13 - n g%5 from by ring]
  set P1 := HJO.extendedSelfQPochhammer (n g%1)
  set I1 := HJO.extendedSelfQPochhammerInv (n g%1)
  set P2 := HJO.extendedSelfQPochhammer (n g%2)
  set I2 := HJO.extendedSelfQPochhammerInv (n g%2)
  set P4 := HJO.extendedSelfQPochhammer (n g%4)
  set I4 := HJO.extendedSelfQPochhammerInv (n g%4)
  set P5 := HJO.extendedSelfQPochhammer (n g%5)
  set I5 := HJO.extendedSelfQPochhammerInv (n g%5)
  set P7 := HJO.extendedSelfQPochhammer (n g%7)
  set I7 := HJO.extendedSelfQPochhammerInv (n g%7)
  set P10 := HJO.extendedSelfQPochhammer (n g%10)
  set I10 := HJO.extendedSelfQPochhammerInv (n g%10)
  set P13 := HJO.extendedSelfQPochhammer (n g%13)
  set I13 := HJO.extendedSelfQPochhammerInv (n g%13)
  set J41 := HJO.extendedSelfQPochhammerInv (n g%4 - n g%1)
  set J52 := HJO.extendedSelfQPochhammerInv (n g%5 - n g%2)
  set J74 := HJO.extendedSelfQPochhammerInv (n g%7 - n g%4)
  set J107 := HJO.extendedSelfQPochhammerInv (n g%10 - n g%7)
  set J102 := HJO.extendedSelfQPochhammerInv (n g%10 - n g%2)
  set A := HJO.extendedSelfQPochhammer (n g%13 - n g%2)
  set J1310 := HJO.extendedSelfQPochhammerInv (n g%13 - n g%10)
  set J135 := HJO.extendedSelfQPochhammerInv (n g%13 - n g%5)
  have e1 : P1 * I1 = 1 := extendedSelfQPochhammer_mul_inv hn1
  have e2 : P2 * I2 = 1 := extendedSelfQPochhammer_mul_inv hn2
  have e4 : P4 * I4 = 1 := extendedSelfQPochhammer_mul_inv hn4
  have e5 : P5 * I5 = 1 := extendedSelfQPochhammer_mul_inv hn5
  have e7 : P7 * I7 = 1 := extendedSelfQPochhammer_mul_inv hn7
  have e10 : P10 * I10 = 1 := extendedSelfQPochhammer_mul_inv hn10
  have e13 : I13 * P13 = 1 := extendedSelfQPochhammerInv_mul_self hn13
  calc P2 * I2 * I2 * (P5 * J52 * I5) * (P1 * I1 * I1) * (P4 * J41 * I4) * (P7 * J74 * I7) *
        (P10 * J107 * J102) * (A * J1310 * J135)
      = (P1 * I1) * (P2 * I2) * (P4 * I4) * (P5 * I5) * (P7 * I7) *
          (I1 * I2 * J41 * J52 * J74 * P10 * J107 * J102 * A * J1310 * J135) := by ring
    _ = I1 * I2 * J41 * J52 * J74 * P10 * J107 * J102 * A * J1310 * J135 := by
        rw [e1, e2, e4, e5, e7]; ring
    _ = (I13 * P13) * (P10 * I10) * (P7 * I7) * (P4 * I4) *
          (I1 * I2 * J41 * J52 * J74 * P10 * J107 * J102 * A * J1310 * J135) := by
        rw [e13, e10, e7, e4]; ring
    _ = _ := by ring

/-- The `b = 8` identity, unconditionally. -/
theorem prod_multiplicand_eight_eq' (n : (finspan {3, 8}).gaps → ℤ) :
    ∏ i : (finspan {3, 8}).gaps, HJO.multiplicand _ 3 8 n i =
      HJO.extendedSelfQPochhammerInv (n g%13) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%13) (n g%10) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%10) (n g%7) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%4) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%4) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%10) (n g%2) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%13 - n g%2) (n g%5 - n g%2)) := by
  rcases lt_or_ge (n g%1) 0 with h | h_1
  · rw [prod_multiplicand_eight, extendedSelfQPochhammer_of_neg h,
      extendedQChoose_eq_zero (A := n g%4) (B := n g%1) (Or.inr h)]
    ring
  rcases lt_or_ge (n g%2) 0 with h | h_2
  · rw [prod_multiplicand_eight, extendedSelfQPochhammer_of_neg h,
      extendedQChoose_eq_zero (A := n g%10) (B := n g%2) (Or.inr h)]
    ring
  rcases lt_or_ge (n g%4) (n g%1) with h | h_3
  · rw [prod_multiplicand_eight,
      extendedSelfQPochhammerInv_of_neg (show n g%4 - n g%1 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%4) (B := n g%1)
        (show n g%4 < n g%1 from by omega)]
    ring
  rcases lt_or_ge (n g%5) (n g%2) with h | h_4
  · rw [prod_multiplicand_eight,
      extendedSelfQPochhammerInv_of_neg (show n g%5 - n g%2 < 0 from by omega),
      extendedQChoose_eq_zero (A := n g%13 - n g%2) (B := n g%5 - n g%2)
        (Or.inr (show n g%5 - n g%2 < 0 from by omega))]
    ring
  rcases lt_or_ge (n g%7) (n g%4) with h | h_5
  · rw [prod_multiplicand_eight,
      extendedSelfQPochhammerInv_of_neg (show n g%7 - n g%4 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%7) (B := n g%4)
        (show n g%7 < n g%4 from by omega)]
    ring
  rcases lt_or_ge (n g%10) (n g%7) with h | h_6
  · rw [prod_multiplicand_eight,
      extendedSelfQPochhammerInv_of_neg (show n g%10 - n g%7 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%10) (B := n g%7)
        (show n g%10 < n g%7 from by omega)]
    ring
  rcases lt_or_ge (n g%13) (n g%10) with h | h_7
  · rw [prod_multiplicand_eight,
      extendedSelfQPochhammerInv_of_neg (show n g%13 - n g%10 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%13) (B := n g%10)
        (show n g%13 < n g%10 from by omega)]
    ring
  rcases lt_or_ge (n g%10) (n g%2) with h | h_8
  · rw [prod_multiplicand_eight,
      extendedSelfQPochhammerInv_of_neg (show n g%10 - n g%2 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%10) (B := n g%2)
        (show n g%10 < n g%2 from by omega)]
    ring
  rcases lt_or_ge (n g%13) (n g%5) with h | h
  · rw [prod_multiplicand_eight,
      extendedSelfQPochhammerInv_of_neg (show n g%13 - n g%5 < 0 from by omega),
      extendedQChoose_eq_zero_of_lt (A := n g%13 - n g%2) (B := n g%5 - n g%2)
        (show n g%13 - n g%2 < n g%5 - n g%2 from by omega)]
    ring
  exact prod_multiplicand_eight_eq n h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 h

/--
§9's factorization of `zNat`'s multiplicand product at `b = 8`: `1/(q)_{r₁}`, times the
`q`-binomials `∏_{i<k} qbinom rᵢ rᵢ₊₁`, times the left side of the sum-to-sum conjecture.
-/
noncomputable def restratifiedEight (n : (finspan {3, 8}).gaps → ℤ) : ℤ⟦X⟧ :=
      HJO.extendedSelfQPochhammerInv (n g%13) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%13) (n g%10) *
        HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%10) (n g%7) *
        (HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%4) (n g%1) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%7) (n g%4) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%10) (n g%2) *
          HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) (n g%13 - n g%2) (n g%5 - n g%2))

theorem prod_multiplicand_eight_eq_restratified (n : (finspan {3, 8}).gaps → ℤ) :
    ∏ i : (finspan {3, 8}).gaps, HJO.multiplicand _ 3 8 n i = restratifiedEight n :=
  prod_multiplicand_eight_eq' n

end eight

end HJOA3
