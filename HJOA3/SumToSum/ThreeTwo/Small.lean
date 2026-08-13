module

import QSeriesLib.Data.Fin.Tuple.Basic
import QSeriesLib.Data.Fin.Tuple.Finset
import QSeriesLib.NumberTheory.HJO.Basic
import QSeriesLib.NumberTheory.HJO.SumToSum.Basic
import QSeriesLib.NumberTheory.NumericalSemigroup.Meta
import QSeriesLib.NumberTheory.QTheory.Basic
import QSeriesLib.NumberTheory.QTheory.Vandermonde
import QSeriesLib.Tactic.Attr.Register
public meta import QSeriesLib.Tactic.ReduceNatFin -- shake: keep
import QSeriesLib.Tactic.ReduceNatFin
public import HJOA3.SumToSum.Box
public import HJOA3.SumToSum.ThreeTwo.Basic

/-!
# Sum-to-sum identities for `b = 5`
-/

@[expose] public section

open Fin Finset Fintype Polynomial NumericalSemigroup NumericalSemigroup.ThreeTwo HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

section five

@[simp] theorem toGaps_one_zero : toGaps 1 0 = g%2 := rfl
@[simp] theorem toGaps_one_one : toGaps 1 1 = g%1 := rfl
@[simp] theorem toGaps_one_two : toGaps 1 2 = g%4 := rfl
@[simp] theorem toGaps_one_three : toGaps 1 3 = g%7 := rfl

/-- The gaps of `(3, 5)` are `1, 2, 4, 7`. -/
theorem Q_three_five (v : (finspan {3, 5}).gaps → ℤ) :
    Q 3 5 v = v g%1 ^ 2 + v g%2 ^ 2 + v g%4 ^ 2 + v g%7 ^ 2 +
      v g%1 * v g%2 - v g%1 * v g%7 + v g%2 * v g%4 - v g%2 * v g%7 := by
  rw [Q, Q'_eq_of_bijective (ThreeTwo.toGaps_bijective 1)]
  simp [Fin.sum_univ_succ, qMatrix_apply, U]
  ring

@[simp] theorem reindex_one_gap_one (r n : Fin 2 → ℕ) : reindex 1 r n g%1 = n 1 := rfl
@[simp] theorem reindex_one_gap_two (r n : Fin 2 → ℕ) : reindex 1 r n g%2 = n 0 := rfl
@[simp] theorem reindex_one_gap_four (r n : Fin 2 → ℕ) : reindex 1 r n g%4 = r 1 := rfl
@[simp] theorem reindex_one_gap_seven (r n : Fin 2 → ℕ) : reindex 1 r n g%7 = r 0 := rfl

@[simp] theorem bound_one_zero (r : Fin 2 → ℕ) : bound 1 r 0 = r 0 := rfl
@[simp] theorem bound_one_one (r : Fin 2 → ℕ) : bound 1 r 1 = r 1 := rfl

theorem qReparam_five (n₁ n₂ r₁ r₂ : ℕ) :
    qReparam (k := 1) ![r₁, r₂] ![n₂, n₁] =
    n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + r₂ ^ 2 + n₁ * n₂ - n₁ * r₁ + n₂ * r₂ - n₂ * r₁ := by
  rw [← Q_reindex_eq_qReparam, Q_three_five]
  simp
  ring

theorem lhsReparam_five (n₁ n₂ r₁ r₂ : ℕ) :
    lhsReparam 1 ![r₁, r₂] ![n₂, n₁] =
    X ^ (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + r₂ ^ 2 +
        n₁ * n₂ - n₁ * r₁ + n₂ * r₂ - n₂ * r₁ : ℤ).toNat *
      qChoose X r₂ n₁ * qChoose X r₁ n₂ := by
  rw [lhsReparam, lhsTermInner, Q'_eq_Q, Q_reindex_eq_qReparam, qReparam_five]
  simp [extendNat, mul_assoc]

theorem lhs_five (r₁ r₂ : ℕ) :
    ∑ᶠ m, lhsTerm 1 ![r₁, r₂] (finspan {3, 3 * 1 + 2}).gaps m =
    ∑ n₂ ∈ range (r₁ + 1), ∑ n₁ ∈ range (r₂ + 1),
      X ^ (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + r₂ ^ 2 +
          n₁ * n₂ - n₁ * r₁ + n₂ * r₂ - n₂ * r₁ : ℤ).toNat *
        qChoose X r₂ n₁ * qChoose X r₁ n₂ := by
  rw [lhs_eq_lhs']
  simp_rw [← lhsReparam_five, lhs', lhsSupport', sum_piFinset_fin_succ, sum_piFinset_fin_zero,
    reduce_tail, bound_one_zero, bound_one_one, Matrix.cons_val, Matrix.empty_eq elim0,
    Matrix.Fin.cons_vecEmpty, Matrix.Fin.cons_vecCons]

theorem rhs_five {r₁ r₂ : ℕ} (hr : r₂ ≤ r₁) :
    ∑ᶠ m, rhsTerm 1 ![r₁, r₂] m =
    ∑ m₁ ∈ range (2 * r₁ + 1),
      X ^ (r₂ ^ 2 + (r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁)) * qChoose X (r₁ + r₂) m₁ := by
  rw [finsum_eq_sum_of_support_subset _ (support_rhsTerm_of_antitone ..)]
  simp only [sum_piFinset_fin_succ, sum_piFinset_fin_zero, rhsTerm_succ,
    sum_univ_succ, sum_univ_zero, add_zero, prod_univ_zero, mul_one,
    reduceNatFin, Matrix.cons_val, Matrix.empty_eq, Matrix.Fin.cons_vecEmpty]

/--
The `b = 5` case of the sum-to-sum conjecture, reduced to an explicit finite identity in
`ℕ[X]`.
-/
theorem five_iff {r₁ r₂ : ℕ} (hr : r₂ ≤ r₁) :
    Conjecture 1 ![r₁, r₂] ↔
    ∑ n₂ ∈ range (r₁ + 1), ∑ n₁ ∈ range (r₂ + 1),
      X (R := ℕ) ^ (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + r₂ ^ 2 +
          n₁ * n₂ - n₁ * r₁ + n₂ * r₂ - n₂ * r₁ : ℤ).toNat *
        qChoose X r₂ n₁ * qChoose X r₁ n₂ =
    ∑ m₁ ∈ range (2 * r₁ + 1),
      X ^ (r₂ ^ 2 + (r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁)) * qChoose X (r₁ + r₂) m₁ := by
  rw [Conjecture, lhs_five, rhs_five hr]

theorem five_identity {r₁ r₂ : ℕ} (hr : r₂ ≤ r₁) :
    ∑ n₂ ∈ range (r₁ + 1), ∑ n₁ ∈ range (r₂ + 1),
      X (R := ℕ) ^ (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + r₂ ^ 2 +
          n₁ * n₂ - n₁ * r₁ + n₂ * r₂ - n₂ * r₁ : ℤ).toNat *
        qChoose X r₂ n₁ * qChoose X r₁ n₂ =
    ∑ m₁ ∈ range (2 * r₁ + 1),
      X ^ (r₂ ^ 2 + (r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁)) * qChoose X (r₁ + r₂) m₁ := by
  classical
  have hexp : ∀ n₁ n₂ : ℕ, n₁ ≤ r₂ → n₂ ≤ r₁ →
      r₂ ^ 2 + (r₁ ^ 2 + (n₁ + n₂) ^ 2 - r₁ * (n₁ + n₂)) + (r₂ - n₁) * n₂ =
      (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + r₂ ^ 2 +
        n₁ * n₂ - n₁ * r₁ + n₂ * r₂ - n₂ * r₁ : ℤ).toNat := by
    intro n₁ n₂ h₁ h₂
    have hle : r₁ * (n₁ + n₂) ≤ r₁ ^ 2 + (n₁ + n₂) ^ 2 := by nlinarith
    have key : (n₁ ^ 2 + n₂ ^ 2 + r₁ ^ 2 + r₂ ^ 2 +
        n₁ * n₂ - n₁ * r₁ + n₂ * r₂ - n₂ * r₁ : ℤ) =
        ((r₂ ^ 2 + (r₁ ^ 2 + (n₁ + n₂) ^ 2 - r₁ * (n₁ + n₂)) + (r₂ - n₁) * n₂ : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle, Nat.cast_sub h₁]
      ring
    rw [key, Int.toNat_natCast]
  have hvanish : ∀ p : ℕ × ℕ, ¬(p.1 ≤ r₂ ∧ p.2 ≤ r₁) →
      X (R := ℕ) ^ (p.1 ^ 2 + p.2 ^ 2 + r₁ ^ 2 + r₂ ^ 2 +
        p.1 * p.2 - p.1 * r₁ + p.2 * r₂ - p.2 * r₁ : ℤ).toNat *
        qChoose X r₂ p.1 * qChoose X r₁ p.2 = 0 := by
    intro p hp
    rcases not_and_or.mp hp with h | h
    · rw [qChoose_eq_zero_of_lt (show r₂ < p.1 from by omega)]; ring
    · rw [qChoose_eq_zero_of_lt (show r₁ < p.2 from by omega)]; ring
  rw [sum_box_eq_sum_antidiagonal (a := r₂) (b := r₁) (N := 2 * r₁) (by omega) _ hvanish]
  refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
  rw [add_comm r₁ r₂, qChoose_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp := (Finset.HasAntidiagonal.mem_antidiagonal
    (self := Finset.Nat.instHasAntidiagonal)).mp hp
  by_cases hb : p.1 ≤ r₂ ∧ p.2 ≤ r₁
  · subst hp
    rw [← mul_assoc, ← mul_assoc, ← pow_add, hexp p.1 p.2 hb.1 hb.2]
  · rw [hvanish p hb]
    rcases not_and_or.mp hb with h | h
    · rw [qChoose_eq_zero_of_lt (show r₂ < p.1 from by omega)]; ring
    · rw [qChoose_eq_zero_of_lt (show r₁ < p.2 from by omega)]; ring

/-- The sum-to-sum conjecture holds for `b = 5`. -/
theorem five {r₁ r₂ : ℕ} (hr : r₂ ≤ r₁) : Conjecture 1 ![r₁, r₂] :=
  (five_iff hr).mpr (five_identity hr)

end five

section eight

@[simp] theorem toGaps_two_zero : toGaps 2 0 = g%2 := rfl
@[simp] theorem toGaps_two_one : toGaps 2 1 = g%5 := rfl
@[simp] theorem toGaps_two_two : toGaps 2 2 = g%1 := rfl
@[simp] theorem toGaps_two_three : toGaps 2 3 = g%4 := rfl
@[simp] theorem toGaps_two_four : toGaps 2 4 = g%7 := rfl
@[simp] theorem toGaps_two_five : toGaps 2 5 = g%10 := rfl
@[simp] theorem toGaps_two_six : toGaps 2 6 = g%13 := rfl

/-- The gaps of `(3, 8)` are `1, 2, 4, 5, 7, 10, 13`. -/
theorem Q_three_eight (v : (finspan {3, 8}).gaps → ℤ) :
    Q 3 8 v = v g%1 ^ 2 + v g%2 ^ 2 + v g%4 ^ 2 + v g%5 ^ 2 + v g%7 ^ 2 + v g%10 ^ 2 +
      v g%13 ^ 2 +
      v g%1 * v g%2 - v g%1 * v g%10 + v g%2 * v g%4 - v g%2 * v g%10 +
      v g%4 * v g%5 - v g%4 * v g%13 + v g%5 * v g%7 - v g%5 * v g%13 := by
  rw [Q, Q'_eq_of_bijective (ThreeTwo.toGaps_bijective 2)]
  simp [Fin.sum_univ_succ, qMatrix_apply, U]
  ring

@[simp] theorem reindex_two_gap_two (r : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    reindex 2 r n g%2 = n 0 := rfl
@[simp] theorem reindex_two_gap_five (r : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    reindex 2 r n g%5 = n 1 := rfl
@[simp] theorem reindex_two_gap_one (r : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    reindex 2 r n g%1 = n 2 := rfl
@[simp] theorem reindex_two_gap_four (r : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    reindex 2 r n g%4 = n 3 := rfl
@[simp] theorem reindex_two_gap_seven (r : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    reindex 2 r n g%7 = r 2 := rfl
@[simp] theorem reindex_two_gap_ten (r : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    reindex 2 r n g%10 = r 1 := rfl
@[simp] theorem reindex_two_gap_thirteen (r : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    reindex 2 r n g%13 = r 0 := rfl

@[simp] theorem bound_two_zero (r : Fin 3 → ℕ) : bound 2 r 0 = r 1 := rfl
@[simp] theorem bound_two_one (r : Fin 3 → ℕ) : bound 2 r 1 = r 0 := rfl
@[simp] theorem bound_two_two (r : Fin 3 → ℕ) : bound 2 r 2 = r 2 := rfl
@[simp] theorem bound_two_three (r : Fin 3 → ℕ) : bound 2 r 3 = r 2 := rfl

theorem qReparam_eight (n₁ n₂ n₄ n₅ r₁ r₂ r₃ : ℕ) :
    qReparam (k := 2) ![r₁, r₂, r₃] ![n₂, n₅, n₁, n₄] =
    n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + r₃ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
      n₁ * n₂ - n₁ * r₂ + n₂ * n₄ - n₂ * r₂ + n₄ * n₅ - n₄ * r₁ + n₅ * r₃ - n₅ * r₁ := by
  rw [← Q_reindex_eq_qReparam, Q_three_eight]
  simp

theorem lhsReparam_eight (n₁ n₂ n₄ n₅ r₁ r₂ r₃ : ℕ) :
    lhsReparam 2 ![r₁, r₂, r₃] ![n₂, n₅, n₁, n₄] =
    X ^ (n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + r₃ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
        n₁ * n₂ - n₁ * r₂ + n₂ * n₄ - n₂ * r₂ + n₄ * n₅ - n₄ * r₁ +
        n₅ * r₃ - n₅ * r₁ : ℤ).toNat *
      qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
      extendedQChoose X ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂) := by
  rw [lhsReparam, lhsTermInner, Q'_eq_Q, Q_reindex_eq_qReparam, qReparam_eight]
  simp [extendNat, Finset.prod_range_succ, mul_assoc]

theorem lhs_eight (r₁ r₂ r₃ : ℕ) :
    ∑ᶠ m, lhsTerm 2 ![r₁, r₂, r₃] (finspan {3, 3 * 2 + 2}).gaps m =
    ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₁ + 1),
    ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
      X ^ (n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + r₃ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
          n₁ * n₂ - n₁ * r₂ + n₂ * n₄ - n₂ * r₂ + n₄ * n₅ - n₄ * r₁ +
          n₅ * r₃ - n₅ * r₁ : ℤ).toNat *
        qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
        extendedQChoose X ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂) := by
  rw [lhs_eq_lhs']
  simp_rw [← lhsReparam_eight, lhs', lhsSupport', sum_piFinset_fin_succ, sum_piFinset_fin_zero,
    reduce_tail, bound_two_zero, bound_two_one, bound_two_two, bound_two_three,
    Matrix.cons_val, Matrix.empty_eq elim0, Matrix.Fin.cons_vecEmpty, Matrix.Fin.cons_vecCons]

theorem rhs_eight {r₁ r₂ r₃ : ℕ} (hr₂₁ : r₂ ≤ r₁) (hr₃₂ : r₃ ≤ r₂) :
    ∑ᶠ m, rhsTerm 2 ![r₁, r₂, r₃] m =
    ∑ m₁ ∈ range (2 * r₁ + 1), ∑ m₂ ∈ range (2 * r₁ + 1),
      X ^ (r₃ ^ 2 + ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂))) *
        qChoose X (r₁ - r₂ + m₂) m₁ * qChoose X (r₂ + r₃) m₂ := by
  rw [finsum_eq_sum_of_support_subset _ (support_rhsTerm_of_antitone ..)]
  simp only [sum_piFinset_fin_succ, sum_piFinset_fin_zero, rhsTerm_succ,
    sum_univ_succ, sum_univ_zero, add_zero, prod_univ_succ, prod_univ_zero, mul_one,
    reduceNatFin, Matrix.cons_val, Matrix.empty_eq, Matrix.Fin.cons_vecEmpty,
    Matrix.Fin.cons_vecCons, reduce_tail, ← add_assoc]

/--
The `b = 8` case of the sum-to-sum conjecture, reduced to an explicit finite identity in
`ℕ[X]`.
-/
theorem eight_iff {r₁ r₂ r₃ : ℕ} (hr₂₁ : r₂ ≤ r₁) (hr₃₂ : r₃ ≤ r₂) :
    Conjecture 2 ![r₁, r₂, r₃] ↔
    ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₁ + 1),
    ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
      X (R := ℕ) ^ (n₁ ^ 2 + n₂ ^ 2 + n₄ ^ 2 + n₅ ^ 2 + r₃ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
          n₁ * n₂ - n₁ * r₂ + n₂ * n₄ - n₂ * r₂ + n₄ * n₅ - n₄ * r₁ +
          n₅ * r₃ - n₅ * r₁ : ℤ).toNat *
        qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
        extendedQChoose X ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂) =
    ∑ m₁ ∈ range (2 * r₁ + 1), ∑ m₂ ∈ range (2 * r₁ + 1),
      X ^ (r₃ ^ 2 + ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂))) *
        qChoose X (r₁ - r₂ + m₂) m₁ * qChoose X (r₂ + r₃) m₂ := by
  rw [Conjecture, lhs_eight, rhs_eight hr₂₁ hr₃₂]

end eight

end HJOA3.SumToSum.ThreeTwo
