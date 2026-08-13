module

public import QSeriesLib.NumberTheory.HJO.SumToSum.Defs
public import QSeriesLib.NumberTheory.QTheory.Basic

/-!
# `q`-Pochhammer identities
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory

namespace HJOA3

/-- `(X; X)_m` has constant term `1`, hence is a unit of `ℤ⟦X⟧`. -/
@[simp] theorem constantCoeff_selfQPochhammer (m : ℕ) :
    constantCoeff (qPochhammer (X : ℤ⟦X⟧) X m) = 1 := by
  rw [qPochhammer, map_prod]
  exact Finset.prod_eq_one fun i _ ↦ by simp

theorem isUnit_selfQPochhammer (m : ℕ) : IsUnit (qPochhammer (X : ℤ⟦X⟧) X m) :=
  IsUnit.of_mul_eq_one _ (mul_invOfUnit _ 1 (by simp))

theorem extendedSelfQPochhammer_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    HJO.extendedSelfQPochhammer m = qPochhammer (X : ℤ⟦X⟧) X m.toNat :=
  if_pos hm

theorem extendedSelfQPochhammer_of_neg {m : ℤ} (hm : m < 0) :
    HJO.extendedSelfQPochhammer m = 0 :=
  if_neg (by omega)

theorem extendedSelfQPochhammerInv_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    HJO.extendedSelfQPochhammerInv m = invOfUnit (qPochhammer (X : ℤ⟦X⟧) X m.toNat) 1 :=
  if_pos hm

theorem extendedSelfQPochhammerInv_of_neg {m : ℤ} (hm : m < 0) :
    HJO.extendedSelfQPochhammerInv m = 0 :=
  if_neg (by omega)

/--
The cancellation that makes the whole approach work: at a nonnegative argument the Pochhammer
symbol and its formal inverse multiply to `1`.
-/
@[simp] theorem extendedSelfQPochhammer_mul_inv {m : ℤ} (hm : 0 ≤ m) :
    HJO.extendedSelfQPochhammer m * HJO.extendedSelfQPochhammerInv m = 1 := by
  rw [extendedSelfQPochhammer_of_nonneg hm, extendedSelfQPochhammerInv_of_nonneg hm]
  exact mul_invOfUnit _ 1 (by rw [constantCoeff_selfQPochhammer]; rfl)

theorem extendedSelfQPochhammerInv_mul_self {m : ℤ} (hm : 0 ≤ m) :
    HJO.extendedSelfQPochhammerInv m * HJO.extendedSelfQPochhammer m = 1 := by
  rw [mul_comm, extendedSelfQPochhammer_mul_inv hm]

theorem isUnit_extendedSelfQPochhammer {m : ℤ} (hm : 0 ≤ m) :
    IsUnit (HJO.extendedSelfQPochhammer m) :=
  IsUnit.of_mul_eq_one _ (extendedSelfQPochhammer_mul_inv hm)

theorem isUnit_extendedSelfQPochhammerInv {m : ℤ} (hm : 0 ≤ m) :
    IsUnit (HJO.extendedSelfQPochhammerInv m) :=
  IsUnit.of_mul_eq_one _ (extendedSelfQPochhammerInv_mul_self hm)

@[simp] theorem extendedSelfQPochhammer_zero : HJO.extendedSelfQPochhammer 0 = 1 := by
  rw [extendedSelfQPochhammer_of_nonneg le_rfl]
  simp

@[simp] theorem extendedSelfQPochhammerInv_zero : HJO.extendedSelfQPochhammerInv 0 = 1 := by
  have h := extendedSelfQPochhammer_mul_inv (m := 0) le_rfl
  rwa [extendedSelfQPochhammer_zero, one_mul] at h

/-- The clearing lemma. -/
theorem extendedQChoose_mul_pochhammer_mul_pochhammer {A B : ℤ} (hB : 0 ≤ B) (hBA : B ≤ A) :
    HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B *
        HJO.extendedSelfQPochhammer B * HJO.extendedSelfQPochhammer (A - B) =
      HJO.extendedSelfQPochhammer A := by
  rw [HJO.SumToSum.extendedQChoose, if_pos ⟨hB.trans hBA, hB⟩,
    extendedSelfQPochhammer_of_nonneg hB, extendedSelfQPochhammer_of_nonneg (by omega),
    extendedSelfQPochhammer_of_nonneg (hB.trans hBA),
    show (A - B).toNat = A.toNat - B.toNat from by omega]
  exact qChoose_mul_qPochhammer_mul_qPochhammer (by omega)

/-- The `ℕ`-argument form, for the factors of `lhsTermInner` that are plain `qChoose`s. -/
theorem qChoose_mul_pochhammer_mul_pochhammer {A B : ℕ} (hBA : B ≤ A) :
    qChoose (X : ℤ⟦X⟧) A B *
        HJO.extendedSelfQPochhammer B * HJO.extendedSelfQPochhammer ((A : ℤ) - B) =
      HJO.extendedSelfQPochhammer A := by
  have h := extendedQChoose_mul_pochhammer_mul_pochhammer
    (A := (A : ℤ)) (B := (B : ℤ)) (by positivity) (by exact_mod_cast hBA)
  rwa [HJO.SumToSum.extendedQChoose, if_pos ⟨by positivity, by positivity⟩,
    Int.toNat_natCast, Int.toNat_natCast] at h

theorem extendedQChoose_eq_zero {A B : ℤ} (h : A < 0 ∨ B < 0) :
    HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B = 0 :=
  if_neg (by omega)

/-- Inside the cone `extendedQChoose` is just `qChoose` on the truncations. -/
theorem extendedQChoose_of_nonneg {A B : ℤ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B = qChoose (X : ℤ⟦X⟧) A.toNat B.toNat :=
  if_pos ⟨hA, hB⟩

/-- The other half of the vanishing, covering `A < B` whether or not `A` is negative. -/
theorem extendedQChoose_eq_zero_of_lt {A B : ℤ} (h : A < B) :
    HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧) A B = 0 := by
  rw [HJO.SumToSum.extendedQChoose]
  split_ifs with hc
  · exact qChoose_eq_zero_of_lt (by omega)
  · rfl

end HJOA3
