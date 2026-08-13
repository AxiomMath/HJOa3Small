module

public import HJOA3.QOne
public import HJOA3.SumToSum.ThreeTwo.Basic

/-!
# Locating the free variables of `ThreeTwo`'s reparametrization
-/

@[expose] public section

open Fin Finset Fintype Polynomial NumericalSemigroup NumericalSemigroup.ThreeTwo HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

@[grind =] lemma val_toGaps_change_inl {k : ℕ} (i : Fin (2 * k)) :
    (toGaps k (change k (.inl i))).val =
      if i.val < k then 3 * i.val + 2 else 3 * (i.val - k) + 1 := by
  grind

/-- The `x`-block free variables sit at the gaps `3j + 2`. -/
theorem extend_reindex_two {k : ℕ} (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) (j : ℕ)
    (hj : j < k) : extendNat (reindex k r n) (3 * j + 2) = n ⟨j, by omega⟩ := by
  have h : 3 * j + 2 = (toGaps k (change k (.inl ⟨j, by omega⟩))).val := by
    rw [val_toGaps_change_inl, if_pos hj]
  rw [h, extend_reindex_apply_inl]

set_option linter.unusedSimpArgs false in
/-- The `y`-block free variables sit at the gaps `3j + 1`. -/
theorem extend_reindex_one {k : ℕ} (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) (j : ℕ)
    (hj : j < k) : extendNat (reindex k r n) (3 * j + 1) = n ⟨k + j, by omega⟩ := by
  have h : 3 * j + 1 = (toGaps k (change k (.inl ⟨k + j, by omega⟩))).val := by
    rw [val_toGaps_change_inl]
    simp only [Fin.val_mk]
    rw [if_neg (show ¬(k + j < k) from by omega)]
    congr 1
    omega
  rw [h, extend_reindex_apply_inl]

/-- The gap `3k + 1` is pinned to `r (Fin.last k)`. -/
theorem extend_reindex_pinned {k : ℕ} (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) :
    extendNat (reindex k r n) (3 * k + 1) = r (Fin.last k) := by
  have h : 3 * k + 1 = (toGaps k (change k (.inr (Fin.last k)))).val := by
    rw [val_toGaps_change_inr]
    simp only [Fin.val_last]
    omega
  rw [h, extend_reindex_apply_inr]

/--
The gap one step below `3j + 2` is `3(j-1) + 2`, or absent when `j = 0` (where the index
truncates to `0`, which is never a gap).
-/
theorem extend_reindex_prev {k : ℕ} (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) (j : Fin k) :
    extendNat (reindex k r n) (3 * j.val - 1) =
      if j.val = 0 then 0 else n ⟨j.val - 1, by omega⟩ := by
  rcases Nat.eq_zero_or_pos j.val with h0 | h0
  · rw [if_pos h0, show 3 * j.val - 1 = 0 from by omega]
    exact dif_neg (NumericalSemigroup.zero_notMem_gaps _)
  · rw [if_neg (by omega), show 3 * j.val - 1 = 3 * (j.val - 1) + 2 from by omega,
      extend_reindex_two r n (j.val - 1) (by omega)]

/--
`ThreeTwo`'s reparametrized summand at `q = 1`, as the product of a `y`-chain factor and an
`x`-chain factor.
-/
theorem lhsReparam_eval_one (k : ℕ) (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) :
    (lhsReparam k r n).eval 1 =
      (∏ i : Fin k, (if h : i.val + 1 < k then n ⟨k + i.val + 1, by omega⟩
        else r (Fin.last k)).choose (n ⟨k + i.val, by omega⟩)) *
      ∏ i : Fin k, extChoose ((r (Fin.castSucc i.rev) : ℤ) -
          (if i.val = 0 then 0 else n ⟨i.val - 1, by omega⟩))
        ((n ⟨i.val, by omega⟩ : ℤ) - (if i.val = 0 then 0 else n ⟨i.val - 1, by omega⟩)) := by
  have h1 : (∏ x : Fin k, (extendNat (reindex k r n) (3 * x.val + 4)).choose
        (extendNat (reindex k r n) (3 * x.val + 1))) =
      ∏ i : Fin k, (if h : i.val + 1 < k then n ⟨k + i.val + 1, by omega⟩
        else r (Fin.last k)).choose (n ⟨k + i.val, by omega⟩) := by
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [extend_reindex_one r n x.val x.isLt]
    congr 1
    split_ifs with h
    · rw [show 3 * x.val + 4 = 3 * (x.val + 1) + 1 from by omega,
        extend_reindex_one r n (x.val + 1) h]
      congr 1
    · rw [show 3 * x.val + 4 = 3 * k + 1 from by omega, extend_reindex_pinned]
  have h2 : (∏ x : Fin k, extChoose ((r (Fin.castSucc x.rev) : ℤ) -
          (extendNat (reindex k r n) (3 * x.val - 1)))
        ((extendNat (reindex k r n) (3 * x.val + 2) : ℤ) -
          (extendNat (reindex k r n) (3 * x.val - 1)))) =
      ∏ i : Fin k, extChoose ((r (Fin.castSucc i.rev) : ℤ) -
          (if i.val = 0 then 0 else n ⟨i.val - 1, by omega⟩))
        ((n ⟨i.val, by omega⟩ : ℤ) - (if i.val = 0 then 0 else n ⟨i.val - 1, by omega⟩)) := by
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [extend_reindex_two r n x.val x.isLt, extend_reindex_prev r n x]
  rw [lhsReparam, lhsTermInner]
  simp only [eval_mul, eval_pow, eval_X, one_pow, one_mul, eval_prod, eval_one_qChoose,
    eval_one_extendedQChoose, prod_range]
  rw [h1, h2]

end HJOA3.SumToSum.ThreeTwo
