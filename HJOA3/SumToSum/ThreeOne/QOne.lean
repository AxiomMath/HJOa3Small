module

public import QSeriesLib.NumberTheory.HJO.SumToSum.Basic
public import HJOA3.QOne
public import HJOA3.SumToSum.ChainFin

/-!
# `thm:q=1` for `b = 3k + 1`, uniformly in `k`
-/

@[expose] public section

open Fin Finset Fintype Polynomial NumericalSemigroup HJO HJO.SumToSum HJO.SumToSum.ThreeOne

namespace HJOA3

/-- The sum-to-sum conjecture at `q = 1`, for every `b ≡ 1 mod 3`. -/
theorem three_one_at_one (k : ℕ) (r : Fin (k + 1) → ℕ) (hanti : Antitone r) :
    (∑ᶠ m, lhsTerm (k + 1) r (finspan {3, 3 * (k + 1) + 1}).gaps m).eval 1 =
      (∑ᶠ m, rhsTerm (k + 1) r m).eval 1 := by
  have hby : ∀ i : Fin (k + 1),
      bound (k + 1) r ⟨k + 1 + i.val, by omega⟩ = r ⟨k, by omega⟩ := by
    intro i
    rw [bound, dif_neg (show ¬(k + 1 + i.val < k + 1) from by omega)]
    congr 1
  have hbx' : ∀ i : Fin (k + 1),
      bound (k + 1) r ⟨i.val, by omega⟩ = r ⟨k - i.val, by omega⟩ := by
    intro i
    rw [bound, dif_pos i.isLt]
    congr 1
    exact Fin.val_injective (by change k + 1 - (i.val + 1) = k - i.val; omega)
  have hn1 : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = ⟨k, by omega⟩ :=
    Fin.val_injective (by change k + 1 - 1 = k; omega)
  have hn2 : ∀ i : Fin (k + 1),
      (⟨k + 1 - 1 - i.val, by omega⟩ : Fin (k + 1)) = ⟨k - i.val, by omega⟩ :=
    fun i ↦ Fin.val_injective (by change k + 1 - 1 - i.val = k - i.val; omega)
  have hmono : Monotone (fun i : Fin (k + 1) ↦ r ⟨k - i.val, by omega⟩) := fun i j hij ↦
    hanti (show (⟨k - j.val, by omega⟩ : Fin (k + 1)) ≤ ⟨k - i.val, by omega⟩ from by
      simp only [Fin.le_def] at hij ⊢
      omega)
  rw [lhs_eq_lhs', lhs', Polynomial.eval_finsetSum,
    finsum_eq_sum_of_support_subset _ (support_rhsTerm_of_antitone (k + 1) r hanti),
    Polynomial.eval_finsetSum]
  simp only [lhsReparam_eq, eval_mul, eval_pow, eval_X, one_pow, one_mul, eval_prod,
    eval_one_qChoose, eval_one_extendedQChoose, rhsTerm, eval_one_rhsTerm_factor]
  rw [sum_mchain_top_last k r hanti,
    Finset.sum_congr rfl (fun x _ ↦ mul_comm _ _), lhsSupport']
  refine Eq.trans (sum_piFinset_split (k := k + 1) _
      (fun y : Fin (k + 1) → ℕ ↦ ∏ i : Fin (k + 1),
        extChoose ((r ⟨k + 1 - 1 - i.val, by omega⟩ : ℤ) -
            (if i.val = 0 then 0 else y ⟨i.val - 1, by omega⟩))
          ((y ⟨i.val, by omega⟩ : ℤ) - (if i.val = 0 then 0 else y ⟨i.val - 1, by omega⟩)))
      (fun y : Fin (k + 1) → ℕ ↦ ∏ i : Fin (k + 1),
        (if h : i.val + 1 < k + 1 then y ⟨i.val + 1, by omega⟩
          else r ⟨k + 1 - 1, by omega⟩).choose (y ⟨i.val, by omega⟩))) ?_
  simp only [hby, hbx', hn1, hn2]
  rw [sum_ychain_top_last (k + 1) (r ⟨k, by omega⟩) (r ⟨k, by omega⟩) le_rfl,
    sum_piFinset_enlarge _ (fun _ : Fin (k + 1) ↦ range (r 0 + 1))
      (fun i x hx ↦ by
        simp only [Finset.mem_range, Nat.lt_succ_iff] at hx ⊢
        exact le_trans hx (hanti (Fin.zero_le _)))
      _ (fun x hx ↦ by
        obtain ⟨i, hi⟩ := hx
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp only [Finset.mem_range, Nat.lt_succ_iff, not_le] at hi
        exact extChoose_eq_zero_of_lt (by exact_mod_cast hi)),
    sum_xchain_explicit (k + 1) (fun i : Fin (k + 1) ↦ r ⟨k - i.val, by omega⟩) (r 0) hmono
      (fun i ↦ hanti (Fin.zero_le _))]
  rw [← yChain_eq_pow (k + 1) (r ⟨k, by omega⟩), List.ofFn_succ]
  have hid := xChain_mul_yChain_eq_mChain
    (List.ofFn fun i : Fin k ↦ r ⟨k - (i.succ : Fin (k + 1)).val, by omega⟩) 0
    (r ⟨k - (0 : Fin (k + 1)).val, by omega⟩) (r ⟨k, by omega⟩)
    (by simpa [List.ofFn_succ] using isChain_zero_cons_ofFn _ hmono)
  simp only [List.length_ofFn] at hid
  have h0 : (⟨k - (0 : Fin (k + 1)).val, by omega⟩ : Fin (k + 1)) = Fin.last k :=
    Fin.val_injective (by simp)
  have h1 : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
  have hlist : (r ⟨k - (0 : Fin (k + 1)).val, by omega⟩ - 0 + r ⟨k, by omega⟩) ::
        gaps (r ⟨k - (0 : Fin (k + 1)).val, by omega⟩ ::
          List.ofFn fun i : Fin k ↦ r ⟨k - (i.succ : Fin (k + 1)).val, by omega⟩) =
      List.ofFn (Fin.cons (2 * r (Fin.last k))
        fun j : Fin k ↦ r j.succ.rev - r j.castSucc.rev) := by
    rw [ofFn_cons,
      ← List.ofFn_succ (f := fun i : Fin (k + 1) ↦ r ⟨k - i.val, by omega⟩), gaps_ofFn, h0, h1]
    congr 1
    · omega
    · congr 1
      funext j
      congr 2 <;> exact Fin.val_injective (by simp [Fin.val_rev])
  rw [hid, hlist]

end HJOA3
