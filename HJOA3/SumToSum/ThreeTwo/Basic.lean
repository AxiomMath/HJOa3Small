module

import QSeriesLib.NumberTheory.HJO.Basic
import QSeriesLib.NumberTheory.HJO.SumToSum.Basic
import QSeriesLib.NumberTheory.QTheory.Basic
public import HJOA3.SumToSum.ThreeTwo.Defs

/-!
# Sum-to-sum identities for `b = 3k + 2`
-/

@[expose] public section

open Finset Fintype Polynomial NumericalSemigroup NumericalSemigroup.ThreeTwo HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo
variable {k : ℕ} (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ)

section lhs_term

/--
Equivalence splitting `Fin (3k+1)` into free variables `Fin (2k)` and the `Fin (k+1)` variables
pinned to `r`.
-/
def change (k : ℕ) : (Fin (2 * k) ⊕ Fin (k + 1)) ≃ Fin (3 * k + 1) :=
  (Equiv.sumCongr (.refl _) Fin.revPerm).trans <|
  finSumFinEquiv.trans <| finCongr (by omega)

@[grind =] lemma change_inl (i : Fin (2 * k)) :
    change k (.inl i) = ⟨i, by omega⟩ := rfl

@[grind =] lemma change_inr (j : Fin (k + 1)) :
    change k (.inr j) = ⟨3 * k - j, by omega⟩ := by
  simp [change, Fin.ext_iff]; omega

@[simp] lemma val_change_inl_lt_two_mul (i : Fin (2 * k)) :
    (change k (.inl i)).val < 2 * k := i.is_lt

@[simp] lemma two_mul_le_val_change_inr (j : Fin (k + 1)) :
    2 * k ≤ (change k (.inr j)).val := by grind

theorem symm_change_apply (i : Fin (3 * k + 1)) :
    (change k).symm i =
      if h : i.val < 2 * k then .inl ⟨i, by omega⟩ else .inr ⟨3 * k - i, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  split_ifs <;> simp [Fin.ext_iff, change]; omega

lemma three_mul_sub_val_change_inr (j : Fin (k + 1)) :
    3 * k - (change k (.inr j)).val = j := by grind

@[grind =] lemma val_toGaps_change_inr (j : Fin (k + 1)) :
    (toGaps k (change k (.inr j))).val = 6 * k + 1 - 3 * j := by grind

@[grind =] lemma int_val_toGaps_change_inr (j : Fin (k + 1)) :
    ((toGaps k (change k (.inr j))).val : ℤ) = 6 * k + 1 - 3 * j := by
  rw [val_toGaps_change_inr]
  omega

lemma val_toGaps_change_inr_sub_val_toGaps_change_inr (i j : Fin (k + 1)) :
    ((toGaps k (change k (.inr i))).val - (toGaps k (change k (.inr j))).val : ℤ) =
    3 * (j - i) := by
  rw [int_val_toGaps_change_inr, int_val_toGaps_change_inr]
  ring

/--
Embedding from `Fin (2 * k) → ℕ` into `G → ℕ`, filling in the top `k + 1` gap variables with
`r`.
-/
def reindex (k : ℕ) (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ)
    (j : (finspan {3, 3 * k + 2}).gaps) : ℕ :=
  (change k).symm (ofGaps k j) |>.elim n r

theorem reindex_injective : (reindex k r).Injective := by
  intro n₁ n₂ h
  funext j
  convert congr($h <| toGaps k <| change k <| .inl j) <;> simp [reindex]

@[simp] theorem reindex_apply_inl (i : Fin (2 * k)) :
    reindex k r n (toGaps k <| change k <| .inl i) = n i := by
  simp [reindex]

@[simp] theorem extend_reindex_apply_inl (i : Fin (2 * k)) :
    extendNat (reindex k r n) (toGaps k <| change k <| .inl i) = n i := by
  simp [← extendNat_subtype]

@[simp] theorem reindex_apply_inr (j : Fin (k + 1)) :
    reindex k r n (toGaps k <| change k <| .inr j) = r j := by
  simp [reindex]

@[simp] theorem extend_reindex_apply_inr (j : Fin (k + 1)) :
    extendNat (reindex k r n) (toGaps k <| change k <| .inr j) = r j := by
  simp [← extendNat_subtype]

theorem reindex_satisfies (j : Fin (k + 1)) :
    extendNat ((reindex k r) n) (6 * k + 1 - 3 * (j : ℕ)) = r j := by
  rw [← val_toGaps_change_inr, ← extendNat_subtype, reindex, ofGaps_toGaps,
    Equiv.symm_apply_apply, Sum.elim_inr]

/-- The summand of the lhs of `Conjecture`, parameterized by the `2 * k` free variables. -/
noncomputable def lhsReparam (k : ℕ) (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) : ℕ[X] :=
  lhsTermInner k r (finspan {3, 3 * k + 2}).gaps <| reindex k r n

theorem lhsTerm_eq_lhsTermInner (k : ℕ) (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) :
    lhsTerm k r (finspan {3, 3 * k + 2}).gaps (reindex k r n) =
      lhsTermInner k r (finspan {3, 3 * k + 2}).gaps (reindex k r n) :=
  if_pos <| reindex_satisfies r n

/-- The per-variable bound for the `2k` free variables. -/
def bound (k : ℕ) (r : Fin (k + 1) → ℕ) (i : Fin (2 * k)) : ℕ :=
  if h : i.val < k then r ⟨k - 1 - i, by omega⟩ else r (Fin.last k)

/-- The support of `lhsTerm` with per-variable bounds, in `G → ℕ` coordinates. -/
def lhsSupport (k : ℕ) (r : Fin (k + 1) → ℕ) :
    Finset ((finspan {3, 3 * k + 2}).gaps → ℕ) :=
  piFinset fun j ↦ (change k).symm (ofGaps k j) |>.elim (range <| bound k r · + 1) ({r ·})

@[simp] lemma mem_lhsSupport_iff (k : ℕ) (r : Fin (k + 1) → ℕ)
    (n : (finspan {3, 3 * k + 2}).gaps → ℕ) :
    n ∈ lhsSupport k r ↔ ∀ i : Fin (3 * k + 1), if h : i.val < 2 * k then
        n (toGaps k i) ≤ bound k r ⟨i, by omega⟩
      else n (toGaps k i) = r ⟨3 * k - i, by omega⟩ := by
  simp_rw [lhsSupport, mem_piFinset, (toGaps_bijective k).surjective.forall,
    ofGaps_toGaps, (change k).surjective.forall, Equiv.symm_apply_apply]
  refine forall_congr' ?_
  simp_rw [Sum.forall, Sum.elim_inl, Sum.elim_inr, dif_pos (val_change_inl_lt_two_mul _),
    mem_range_succ_iff, change_inl, dif_neg (not_lt_of_ge <| two_mul_le_val_change_inr _),
    three_mul_sub_val_change_inr, mem_singleton]
  solve_by_elim

/-- The support of `lhsReparam` with per-variable bounds, in `Fin (2 * k) → ℕ` coordinates. -/
def lhsSupport' (k : ℕ) (r : Fin (k + 1) → ℕ) : Finset (Fin (2 * k) → ℕ) :=
  piFinset (range <| bound k r · + 1)

/-- The lhs of `Conjecture`, summing over the `2 * k` free variables. -/
noncomputable def lhs' (k : ℕ) (r : Fin (k + 1) → ℕ) : ℕ[X] :=
  ∑ n ∈ lhsSupport' k r, lhsReparam k r n

/-- Embedding version of `reindex`. -/
def reindexEmbedding (k : ℕ) (r : Fin (k + 1) → ℕ) :
    (Fin (2 * k) → ℕ) ↪ ((finspan {3, 3 * k + 2}).gaps → ℕ) where
  toFun := reindex k r
  inj' := reindex_injective r

@[simp] theorem coe_reindexEmbedding : reindexEmbedding k r = reindex k r := rfl

theorem map_reindexEmbedding_lhsSupport'_eq_lhsSupport (k : ℕ) (r : Fin (k + 1) → ℕ) :
    (lhsSupport' k r).map (reindexEmbedding k r) = lhsSupport k r := by
  ext n
  simp [reindex, lhsSupport', mem_lhsSupport_iff, (toGaps_bijective k).surjective.forall,
      -Subtype.forall, ofGaps_toGaps, funext_iff, (change k).surjective.forall,
      change_inl, change_inr]
  simpa using ⟨by grind, fun h ↦ ⟨fun i ↦ n (toGaps k ⟨i, by omega⟩), by grind⟩⟩

theorem support_lhsTerm (k : ℕ) (r : Fin (k + 1) → ℕ) :
    (lhsTerm k r (finspan {3, 3 * k + 2}).gaps).support ⊆ lhsSupport k r := fun n hn ↦ by
  simp_rw [Function.mem_support, lhsTerm, ite_ne_right_iff, lhsTermInner,
    mul_ne_zero_iff, prod_ne_zero_iff, mem_range, qChoose_X_ne_zero_iff,
    extendedQChoose_X_ne_zero_iff, mem_univ, true_imp_iff, sub_nonneg,
    sub_le_sub_iff_right, Nat.cast_le] at hn
  simp_rw [mem_coe, mem_lhsSupport_iff, bound, extendNat_subtype n]
  intro i
  split_ifs with hi1 hi2
  · have h := (hn.2.2 ⟨(i : ℕ), hi2⟩).2
    rw [val_toGaps_apply, if_pos hi2]
    refine h.trans (le_of_eq (congrArg r ?_))
    ext
    simp only [Fin.val_castSucc, Fin.val_rev]
    omega
  · have chain : ∀ m₂ ≤ k, ∀ m₁ ≤ m₂,
        extendNat n (3 * m₁ + 1) ≤ extendNat n (3 * m₂ + 1) := by
      intro m₂
      induction m₂ with
      | zero => intro _ m₁ h; rw [Nat.le_zero.mp h]
      | succ m₂ ih =>
          intro hm₂ m₁ hm₁
          rcases Nat.lt_or_ge m₁ (m₂ + 1) with h | h
          · refine (ih (by omega) m₁ (by omega)).trans ?_
            refine (hn.2.1.2 m₂ (by omega)).trans (le_of_eq ?_)
            congr 1
          · rw [show m₁ = m₂ + 1 from by omega]
    have hlast : extendNat n (3 * k + 1) = r (Fin.last k) := by
      have h := hn.1 (Fin.last k)
      simp only [Fin.val_last, show 6 * k + 1 - 3 * k = 3 * k + 1 from by omega] at h
      simpa using h
    rw [val_toGaps_apply, if_neg hi2, ← hlast]
    exact chain k le_rfl _ (by omega)
  · have h := hn.1 ⟨3 * k - i.val, by omega⟩
    simp only [show 6 * k + 1 - 3 * (3 * k - i.val) = 3 * (i.val - k) + 1 from by omega] at h
    rw [val_toGaps_apply, if_neg (show ¬ ((i : ℕ) < k) from by omega), ← h]

theorem lhs_eq_lhs' (k : ℕ) (r : Fin (k + 1) → ℕ) :
    ∑ᶠ m, lhsTerm k r (finspan {3, 3 * k + 2}).gaps m = lhs' k r := by
  unfold lhs' lhsReparam
  rw [finsum_eq_sum_of_support_subset _ (support_lhsTerm ..),
    ← map_reindexEmbedding_lhsSupport'_eq_lhsSupport, sum_map, coe_reindexEmbedding]
  simp only [lhsTerm_eq_lhsTermInner]

/--
A reparametrized form of `Q`, split into the free-free, pinned-pinned and free-pinned blocks.
-/
def qReparam (k : ℕ) (r : Fin (k + 1) → ℕ) (n : Fin (2 * k) → ℕ) : ℤ :=
  ∑ i : Fin (2 * k), ∑ j : Fin (2 * k),
    U 3 (3 * k + 2) (toGaps k (change k <| .inl j) - toGaps k (change k <| .inl i)) *
      n i * n j +
  ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), U 3 (3 * k + 2) (3 * (i - j)) * r i * r j +
  ∑ i : Fin (2 * k), ∑ j : Fin (k + 1),
    U 3 (3 * k + 2) (6 * k + 1 - 3 * j - toGaps k (change k <| .inl i)) * n i * r j

@[simp] theorem qMatrix_inr_inl_eq_zero {k : ℕ} (i : Fin (k + 1)) (j : Fin (2 * k)) :
    qMatrix (finspan {3, 3 * k + 2}).gaps 3 (3 * k + 2)
      (toGaps k <| change k <| .inr i) (toGaps k <| change k <| .inl j) = 0 :=
  U_eq_zero_of_neg <| by simp [change_inr, change_inl, val_toGaps_apply]; grind

theorem Q_reindex_eq_qReparam :
    Q 3 (3 * k + 2) (reindex k r n ·) = qReparam k r n := by
  rw [Q, Q'_eq_of_bijective (toGaps_bijective k |>.comp (change k).bijective)]
  simp_rw [sum_sum_type, sum_add_distrib, Function.comp_apply,
    reindex_apply_inl, reindex_apply_inr, qMatrix_inr_inl_eq_zero,
    zero_mul, sum_const_zero, zero_add,
    qMatrix_apply, val_toGaps_change_inr_sub_val_toGaps_change_inr,
    int_val_toGaps_change_inr, qReparam]
  rw [add_right_comm]

end lhs_term

section rhs_term

theorem rhsTerm_succ (k : ℕ) (r : Fin (k + 1 + 1) → ℕ) (m : Fin (k + 1) → ℕ) :
    rhsTerm (k + 1) r m =
      X ^ (r (Fin.last (k + 1)) ^ 2 +
        ∑ i : Fin (k + 1), (r i.castSucc ^ 2 + m i ^ 2 - r i.castSucc * m i)) *
      (∏ i : Fin k, qChoose X
        (r i.castSucc.castSucc - r i.succ.castSucc + m i.succ) (m i.castSucc)) *
      qChoose X (r (Fin.last k).castSucc + r (Fin.last (k + 1))) (m (Fin.last k)) := by
  rw [rhsTerm, Fin.prod_univ_castSucc, mul_assoc]
  grind

/-- For antitone `r`, every `m` in the support of `rhsTerm` is bounded by `2 * r 0`. -/
theorem support_rhsTerm_of_antitone (k : ℕ) (r : Fin (k + 1) → ℕ)
    (hr : Antitone r := by simp_all) :
    (rhsTerm k r).support ⊆
    (piFinset fun _ ↦ range (2 * r 0 + 1) : Finset (Fin k → ℕ)) := fun m hm ↦ by
  obtain _ | k := k
  · exact Finset.mem_coe.mpr (mem_piFinset.mpr fun i ↦ i.elim0)
  simp_rw [Function.mem_support, rhsTerm_succ,
    mul_ne_zero_iff, prod_ne_zero_iff, qChoose_X_ne_zero_iff, mem_univ, true_imp_iff] at hm
  simp only [two_mul, coe_piFinset, coe_range, Set.mem_pi, Set.mem_univ, Set.mem_Iio,
    Order.lt_add_one_iff, forall_const]
  have key : ∀ i : Fin (k + 1), m i ≤ r i.castSucc + r (Fin.last (k + 1)) := by
    refine Fin.reverseInduction hm.2 fun i ih ↦ ?_
    refine (hm.1.2 i).trans ((Nat.add_le_add_left ih _).trans (le_of_eq ?_))
    rw [← add_assoc, Nat.sub_add_cancel (hr (by grind))]
  exact fun i ↦ (key i).trans (Nat.add_le_add (hr (by grind)) (hr (by grind)))

end rhs_term

end HJOA3.SumToSum.ThreeTwo
