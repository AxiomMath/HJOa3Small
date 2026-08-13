module

public import HJOA3.SumToSum.ChainFin
public import HJOA3.SumToSum.ThreeTwo.Reindex

/-!
# `thm:q=1` for `b ≡ 2 mod 3`, uniformly in `k`
-/

@[expose] public section

open Fin Finset Fintype Polynomial NumericalSemigroup NumericalSemigroup.ThreeTwo HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

/--
`eval 1` of a factor of `ThreeTwo.rhsTerm`, with the `choose` kept *outside* the conditional.
-/
theorem eval_one_rhsTerm_factor {k : ℕ} (r : Fin (k + 1) → ℕ) (m : Fin k → ℕ) (i : Fin k) :
    (if h : i.val + 1 = k then qChoose (X : ℕ[X]) (r i.castSucc + r (Fin.last k)) (m i)
      else qChoose X (r i.castSucc - r i.succ + m ⟨i.val + 1, by omega⟩)
        (m i)).eval 1 =
    (if h : i.val + 1 = k then r i.castSucc + r (Fin.last k)
      else r i.castSucc - r i.succ + m ⟨i.val + 1, by omega⟩).choose (m i) := by
  split_ifs <;> simp

/-- The sum-to-sum conjecture at `q = 1`, for every `b ≡ 2 mod 3`. -/
theorem three_two_at_one (k : ℕ) (r : Fin (k + 1) → ℕ) (hanti : Antitone r) :
    (∑ᶠ m, lhsTerm k r (finspan {3, 3 * k + 2}).gaps m).eval 1 =
      (∑ᶠ m, rhsTerm k r m).eval 1 := by
  rw [lhs_eq_lhs', lhs', Polynomial.eval_finsetSum,
    finsum_eq_sum_of_support_subset _ (support_rhsTerm_of_antitone k r hanti),
    Polynomial.eval_finsetSum]
  obtain _ | K := k
  · simp [lhsSupport', lhsReparam_eval_one, rhsTerm]
  have hbx : ∀ i : Fin (K + 1),
      bound (K + 1) r ⟨i.val, by omega⟩ = r (Fin.castSucc i.rev) := by
    intro i
    rw [bound, dif_pos i.isLt]
    congr 1
    exact Fin.val_injective (by simp only [Fin.val_castSucc, Fin.val_rev]; omega)
  have hby : ∀ i : Fin (K + 1),
      bound (K + 1) r ⟨K + 1 + i.val, by omega⟩ = r (Fin.last (K + 1)) := fun i ↦
    dif_neg (show ¬(K + 1 + i.val < K + 1) from by omega)
  have hmono : Monotone (fun i : Fin (K + 1) ↦ r (Fin.castSucc i.rev)) := fun i j hij ↦
    hanti (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_rev] at hij ⊢; omega)
  have hle : ∀ i : Fin (K + 1), r (Fin.castSucc i.rev) ≤ r 0 := fun _ ↦ hanti (Fin.zero_le _)
  simp only [lhsReparam_eval_one, rhsTerm, eval_mul, eval_pow, eval_X, one_pow, one_mul,
    eval_prod, eval_one_rhsTerm_factor]
  refine Eq.trans ?_ (sum_mchain_top_last_sep K (fun i : Fin (K + 1) ↦ r i.castSucc)
    (r (Fin.last (K + 1))) (2 * r 0)
    (fun i j hij ↦ hanti (by simpa only [Fin.le_def, Fin.val_castSucc] using hij))
    (by
      rw [Fin.castSucc_zero]
      have := hanti (Fin.zero_le (Fin.last (K + 1)))
      omega)).symm
  rw [Finset.sum_congr rfl (fun x _ ↦ mul_comm _ _), lhsSupport']
  refine Eq.trans (sum_piFinset_split (k := K + 1) _
      (fun y : Fin (K + 1) → ℕ ↦ ∏ i : Fin (K + 1),
        extChoose ((r (Fin.castSucc i.rev) : ℤ) -
            (if i.val = 0 then 0 else y ⟨i.val - 1, by omega⟩))
          ((y ⟨i.val, by omega⟩ : ℤ) - (if i.val = 0 then 0 else y ⟨i.val - 1, by omega⟩)))
      (fun y : Fin (K + 1) → ℕ ↦ ∏ i : Fin (K + 1),
        (if h : i.val + 1 < K + 1 then y ⟨i.val + 1, by omega⟩
          else r (Fin.last (K + 1))).choose (y ⟨i.val, by omega⟩))) ?_
  simp only [hbx, hby]
  rw [sum_ychain_top_last (K + 1) (r (Fin.last (K + 1))) (r (Fin.last (K + 1))) le_rfl,
    sum_piFinset_enlarge _ (fun _ : Fin (K + 1) ↦ range (r 0 + 1))
      (fun i x hx ↦ by
        simp only [Finset.mem_range, Nat.lt_succ_iff] at hx ⊢
        exact le_trans hx (hle i))
      _ (fun x hx ↦ by
        obtain ⟨i, hi⟩ := hx
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp only [Finset.mem_range, Nat.lt_succ_iff, not_le] at hi
        exact extChoose_eq_zero_of_lt (by exact_mod_cast hi)),
    sum_xchain_explicit (K + 1) (fun i : Fin (K + 1) ↦ r (Fin.castSucc i.rev)) (r 0) hmono hle,
    ← yChain_eq_pow (K + 1) (r (Fin.last (K + 1))), List.ofFn_succ]
  have hid := xChain_mul_yChain_eq_mChain
    (List.ofFn fun i : Fin K ↦ r (Fin.castSucc (Fin.rev (i.succ : Fin (K + 1))))) 0
    (r (Fin.castSucc (Fin.rev (0 : Fin (K + 1))))) (r (Fin.last (K + 1)))
    (by simpa [List.ofFn_succ] using isChain_zero_cons_ofFn _ hmono)
  simp only [List.length_ofFn] at hid
  rw [hid, ofFn_cons,
    ← List.ofFn_succ (f := fun i : Fin (K + 1) ↦ r (Fin.castSucc i.rev)), gaps_ofFn]
  congr 1

end HJOA3.SumToSum.ThreeTwo
