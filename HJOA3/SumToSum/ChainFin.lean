module

public import QSeriesLib.Data.Fin.Tuple.Finset
public import HJOA3.FlagStraightening
public import HJOA3.QOne
public import HJOA3.SumToSum.Box

/-!
# Chain sums in `Fin`-tuple form
-/

@[expose] public section

open Fin Finset Fintype

namespace HJOA3

/--
The number of chains `z_{k-1} ≤ ⋯ ≤ z₀ ≤ S` is `(k+1) ^ S`, as a sum over a box in `ℕ ^ k`
whose bound `N` is *decoupled* from the chain top `S`.
-/
theorem sum_chain_fin : ∀ (k S N : ℕ), S ≤ N →
    ∑ z ∈ Fintype.piFinset (fun _ : Fin k ↦ range (N + 1)),
      ∏ j : Fin k, ((Fin.cons S z : Fin (k + 1) → ℕ) j.castSucc).choose
        ((Fin.cons S z : Fin (k + 1) → ℕ) j.succ) = (k + 1) ^ S
  | 0, S, N, _ => by simp
  | k + 1, S, N, hSN => by
      rw [Fintype.sum_piFinset_fin_succ]
      have hterm : ∀ a ∈ range (N + 1),
          ∑ w ∈ Fintype.piFinset (Fin.tail fun _ : Fin (k + 1) ↦ range (N + 1)),
            ∏ j : Fin (k + 1),
              ((Fin.cons S (Fin.cons a w) : Fin (k + 1 + 1) → ℕ) j.castSucc).choose
                ((Fin.cons S (Fin.cons a w) : Fin (k + 1 + 1) → ℕ) j.succ) =
            S.choose a * (k + 1) ^ a := by
        intro a ha
        have haN : a ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [show (Fin.tail fun _ : Fin (k + 1) ↦ range (N + 1)) = fun _ : Fin k ↦ range (N + 1) from
          rfl, ← sum_chain_fin k a N haN, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [Fin.prod_univ_succ]
        simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
      rw [Finset.sum_congr rfl hterm,
        sum_range_shrink hSN _ (fun i hi ↦ by rw [Nat.choose_eq_zero_of_lt hi]; ring),
        sum_range_choose_mul_pow S (k + 1)]

/-- The `x`-chain in `Fin`-tuple form: the box sum equals `xChain b (List.ofFn ρ)`. -/
theorem sum_xchain_fin : ∀ (k : ℕ) (ρ : Fin k → ℕ) (b N : ℕ), b ≤ N → Monotone ρ →
    (∀ i, b ≤ ρ i) → (∀ i, ρ i ≤ N) →
    ∑ x ∈ Fintype.piFinset (fun _ : Fin k ↦ range (N + 1)),
      ∏ i : Fin k, extChoose ((ρ i : ℤ) - (Fin.cons b x : Fin (k + 1) → ℕ) i.castSucc)
        (((Fin.cons b x : Fin (k + 1) → ℕ) i.succ : ℤ) -
          (Fin.cons b x : Fin (k + 1) → ℕ) i.castSucc) =
      xChain b (List.ofFn ρ)
  | 0, ρ, b, N, _, _, _, _ => by simp
  | k + 1, ρ, b, N, hbN, hmono, hb, hN => by
      rw [Fintype.sum_piFinset_fin_succ, List.ofFn_succ, xChain_cons]
      rw [← sum_range_shift_of_vanish (n := b) (N := N) hbN _ ?vanish]
      · rw [sum_range_shrink (show ρ 0 - b ≤ N - b from by
              have := hN 0; omega) _ ?shrink]
        · refine Finset.sum_congr rfl fun d hd ↦ ?_
          have hd' : d ≤ ρ 0 - b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
          have hρ0 : b ≤ ρ 0 := hb 0
          have hρN : ρ 0 ≤ N := hN 0
          rw [show (Fin.tail fun _ : Fin (k + 1) ↦ range (N + 1)) =
            fun _ : Fin k ↦ range (N + 1) from rfl,
            ← sum_xchain_fin k (fun i ↦ ρ i.succ) (b + d) N (by omega)
              (fun i j hij ↦ hmono (Fin.succ_le_succ_iff.mpr hij))
              (fun i ↦ by
                have h0 : ρ 0 ≤ ρ i.succ := hmono (Fin.zero_le _)
                omega)
              (fun i ↦ hN _),
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ ↦ ?_
          rw [Fin.prod_univ_succ]
          simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
          rw [extChoose_of_nonneg (by omega) (by push_cast; omega)]
          congr 2 <;> omega
        · intro i hi
          refine Finset.sum_eq_zero fun w _ ↦ ?_
          rw [Fin.prod_univ_succ]
          simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
          rw [extChoose_of_nonneg (by have := hb 0; omega) (by push_cast; omega),
            Nat.choose_eq_zero_of_lt (by omega)]
          ring
      · intro a ha
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        rw [Fin.prod_univ_succ]
        simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        rw [extChoose_of_neg (Or.inr (by omega))]
        ring

/-- The `m`-chain in `Fin`-tuple form: the box sum equals `mChain c (List.ofFn g)`. -/
theorem sum_mchain_fin : ∀ (k : ℕ) (g : Fin k → ℕ) (c N : ℕ), c + ∑ i, g i ≤ N →
    ∑ z ∈ Fintype.piFinset (fun _ : Fin k ↦ range (N + 1)),
      ∏ j : Fin k, (g j + (Fin.cons c z : Fin (k + 1) → ℕ) j.castSucc).choose
        ((Fin.cons c z : Fin (k + 1) → ℕ) j.succ) = mChain c (List.ofFn g)
  | 0, g, c, N, _ => by simp
  | k + 1, g, c, N, hN => by
      have hsplit : ∑ i, g i = g 0 + ∑ i : Fin k, g i.succ := Fin.sum_univ_succ g
      rw [Fintype.sum_piFinset_fin_succ, List.ofFn_succ, mChain_cons,
        sum_range_shrink (show g 0 + c ≤ N from by omega) _ ?shrink]
      · refine Finset.sum_congr rfl fun a ha ↦ ?_
        have ha' : a ≤ g 0 + c := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [show (Fin.tail fun _ : Fin (k + 1) ↦ range (N + 1)) =
          fun _ : Fin k ↦ range (N + 1) from rfl,
          ← sum_mchain_fin k (fun i ↦ g i.succ) a N (by omega), Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [Fin.prod_univ_succ]
        simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
      · intro i hi
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        rw [Fin.prod_univ_succ]
        simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        ring

/-- `Fin.cons` evaluated at a `castSucc` index, in explicit-index form. -/
theorem cons_castSucc {k : ℕ} (S : ℕ) (y : Fin k → ℕ) (j : Fin k) :
    (Fin.cons S y : Fin (k + 1) → ℕ) j.castSucc =
      if j.val = 0 then S else y ⟨j.val - 1, by omega⟩ := by
  rcases Nat.eq_zero_or_pos j.val with h0 | h0
  · rw [if_pos h0]
    have h : j.castSucc = (0 : Fin (k + 1)) := Fin.val_injective (by change j.val = 0; omega)
    rw [h, Fin.cons_zero]
  · rw [if_neg (by omega)]
    have h : j.castSucc = (⟨j.val - 1, by omega⟩ : Fin k).succ :=
      Fin.val_injective (by change j.val = j.val - 1 + 1; omega)
    rw [h, Fin.cons_succ]

/-- The `y`-half of the `q = 1` left side, in the index style of `lhsReparam_eq`. -/
theorem sum_ychain_top_last (k S N : ℕ) (hSN : S ≤ N) :
    ∑ y ∈ Fintype.piFinset (fun _ : Fin k ↦ range (N + 1)),
      ∏ i : Fin k, (if h : i.val + 1 < k then y ⟨i.val + 1, h⟩ else S).choose (y i) =
      (k + 1) ^ S := by
  rw [sum_piFinset_const_comp _ Fin.revPerm, ← sum_chain_fin k S N hSN]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← Equiv.prod_comp Fin.revPerm
    (fun j ↦ ((Fin.cons S y : Fin (k + 1) → ℕ) j.castSucc).choose
      ((Fin.cons S y : Fin (k + 1) → ℕ) j.succ))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hrev : (Fin.revPerm i).val = k - 1 - i.val := by
    change (Fin.rev i).val = k - 1 - i.val
    rw [Fin.val_rev]
    omega
  rw [Fin.cons_succ, cons_castSucc]
  have hi' : i.val < k := i.isLt
  split_ifs <;> first | rfl | omega

/-- `gaps` of a `List.ofFn` list is the list of consecutive differences. -/
theorem gaps_ofFn : ∀ (k : ℕ) (ρ : Fin (k + 1) → ℕ),
    gaps (List.ofFn ρ) = List.ofFn fun j : Fin k ↦ ρ j.succ - ρ j.castSucc
  | 0, ρ => by simp
  | k + 1, ρ => by
      rw [List.ofFn_succ, List.ofFn_succ (f := fun i : Fin (k + 1) ↦ ρ i.succ), gaps_cons_cons,
        ← List.ofFn_succ (f := fun i : Fin (k + 1) ↦ ρ i.succ),
        gaps_ofFn k (fun i ↦ ρ i.succ),
        List.ofFn_succ (f := fun j : Fin (k + 1) ↦ ρ j.succ - ρ j.castSucc)]
      simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.succ_castSucc]

/-- The consecutive differences of a monotone `Fin`-indexed sequence telescope. -/
theorem sum_consecutive_sub : ∀ (k : ℕ) (ρ : Fin (k + 1) → ℕ), Monotone ρ →
    ∑ j : Fin k, (ρ j.succ - ρ j.castSucc) = ρ (Fin.last k) - ρ 0
  | 0, ρ, _ => by simp
  | k + 1, ρ, hmono => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.succ_castSucc]
      rw [sum_consecutive_sub k (fun i ↦ ρ i.castSucc)
        (fun i j hij ↦ hmono (by simp only [Fin.le_def, Fin.val_castSucc]; exact hij))]
      have h1 : ρ 0 ≤ ρ (Fin.last k).castSucc := hmono (Fin.zero_le _)
      have h2 : ρ (Fin.last k).castSucc ≤ ρ (Fin.last (k + 1)) :=
        hmono (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]; omega)
      have h3 : ((Fin.last k).succ : Fin (k + 2)) = Fin.last (k + 1) := rfl
      rw [h3]
      simp only [Fin.castSucc_zero]
      omega

/-- Reversing an antitone sequence makes it monotone. -/
theorem monotone_comp_rev {k : ℕ} {r : Fin k → ℕ} (hanti : Antitone r) :
    Monotone fun j : Fin k ↦ r j.rev := fun _ _ hij ↦ hanti (Fin.rev_le_rev.mpr hij)

/-- `List.ofFn` of a `Fin.cons`. -/
theorem ofFn_cons {k : ℕ} (a : ℕ) (g : Fin k → ℕ) :
    List.ofFn (Fin.cons a g : Fin (k + 1) → ℕ) = a :: List.ofFn g := by
  simp [List.ofFn_succ]

/-- The gap data for the `m`-side satisfies `sum_mchain_fin`'s bound hypothesis. -/
theorem mchain_gap_sum_le {k : ℕ} (r : Fin (k + 1) → ℕ) (s N : ℕ) (hanti : Antitone r)
    (hN : r 0 + s ≤ N) :
    0 + ∑ j : Fin (k + 1), (Fin.cons (r (Fin.last k) + s)
      (fun j : Fin k ↦ r (Fin.rev j.succ) - r (Fin.rev j.castSucc)) : Fin (k + 1) → ℕ) j ≤
    N := by
  have hmono := monotone_comp_rev hanti
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_add]
  rw [sum_consecutive_sub k (fun j : Fin (k + 1) ↦ r j.rev) hmono]
  have h1 : r (Fin.rev 0) ≤ r (Fin.rev (Fin.last k)) := hmono (Fin.zero_le _)
  have h2 : (Fin.rev (0 : Fin (k + 1))) = Fin.last k :=
    Fin.val_injective (by simp)
  have h3 : (Fin.rev (Fin.last k) : Fin (k + 1)) = 0 :=
    Fin.val_injective (by simp)
  rw [h2, h3] at h1 ⊢
  omega

/-- `Fin.cons` at a general index, in explicit-index form. -/
theorem cons_apply {k : ℕ} (a : ℕ) (g : Fin k → ℕ) (i : Fin (k + 1)) :
    (Fin.cons a g : Fin (k + 1) → ℕ) i =
      if h : i.val = 0 then a else g ⟨i.val - 1, by omega⟩ := by
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp

/-- The `m`-side translation. -/
theorem sum_mchain_top_last_sep (k : ℕ) (r : Fin (k + 1) → ℕ) (s N : ℕ) (hanti : Antitone r)
    (hN : r 0 + s ≤ N) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin (k + 1) ↦ range (N + 1)),
      ∏ i : Fin (k + 1), (if h : i.val + 1 = k + 1 then r i + s
        else r i - r ⟨i.val + 1, by omega⟩ + m ⟨i.val + 1, by omega⟩).choose (m i) =
      mChain 0 (List.ofFn (Fin.cons (r (Fin.last k) + s)
        (fun j : Fin k ↦ r (Fin.rev j.succ) - r (Fin.rev j.castSucc)))) := by
  have hrv : ∀ j : Fin (k + 1), (Fin.rev j).val = k - j.val := fun j ↦ by
    rw [Fin.val_rev]; omega
  rw [sum_piFinset_const_comp _ Fin.revPerm,
    ← sum_mchain_fin (k + 1) _ 0 N (mchain_gap_sum_le r s N hanti hN)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hi : i.val < k + 1 := i.isLt
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev, Fin.cons_succ, cons_castSucc]
  simp only [cons_apply, hrv]
  split_ifs with h1 h2
  · rw [show Fin.rev i = Fin.last k from
      Fin.val_injective (by simp only [hrv, Fin.val_last]; omega), add_zero]
  · omega
  · omega
  · rw [show Fin.rev (⟨k - i.val + 1, by omega⟩ : Fin (k + 1)) =
          (⟨i.val - 1, by omega⟩ : Fin (k + 1)) from
        Fin.val_injective (by simp only [hrv]; omega),
      show (⟨k - i.val + 1, by omega⟩ : Fin (k + 1)) =
          Fin.rev ((⟨i.val - 1, by omega⟩ : Fin k).castSucc) from
        Fin.val_injective (by simp only [hrv, Fin.val_castSucc]; omega),
      show Fin.rev i = Fin.rev ((⟨i.val - 1, by omega⟩ : Fin k).succ) from
        Fin.val_injective (by simp only [hrv, Fin.val_succ]; omega)]

/-- The `m`-side translation for `b ≡ 1 mod 3`. -/
theorem sum_mchain_top_last (k : ℕ) (r : Fin (k + 1) → ℕ) (hanti : Antitone r) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin (k + 1) ↦ range (2 * r 0 + 1)),
      ∏ i : Fin (k + 1), (if h : i.val + 1 = k + 1 then 2 * r i
        else r i - r ⟨i.val + 1, by omega⟩ + m ⟨i.val + 1, by omega⟩).choose (m i) =
      mChain 0 (List.ofFn (Fin.cons (2 * r (Fin.last k))
        (fun j : Fin k ↦ r (Fin.rev j.succ) - r (Fin.rev j.castSucc)))) := by
  rw [two_mul (r (Fin.last k))]
  refine Eq.trans (Finset.sum_congr rfl fun m _ ↦ Finset.prod_congr rfl fun i _ ↦ ?_)
    (sum_mchain_top_last_sep k r (r (Fin.last k)) (2 * r 0) hanti
      (by have := hanti (Fin.zero_le (Fin.last k)); omega))
  split_ifs with h
  · rw [show i = Fin.last k from Fin.val_injective (by simp only [Fin.val_last]; omega), two_mul]
  · rfl

/-- The `x`-chain in explicit-index form, matching `lhsReparam_eq`'s second product. -/
theorem sum_xchain_explicit (k : ℕ) (ρ : Fin k → ℕ) (N : ℕ) (hmono : Monotone ρ)
    (hN : ∀ i, ρ i ≤ N) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin k ↦ range (N + 1)),
      ∏ i : Fin k, extChoose ((ρ i : ℤ) - (if i.val = 0 then 0 else x ⟨i.val - 1, by omega⟩))
        ((x ⟨i.val, by omega⟩ : ℤ) - (if i.val = 0 then 0 else x ⟨i.val - 1, by omega⟩)) =
      xChain 0 (List.ofFn ρ) := by
  rw [← sum_xchain_fin k ρ 0 N (Nat.zero_le _) hmono (fun _ ↦ Nat.zero_le _) hN]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.prod_congr rfl fun i _ ↦ ?_
  rw [cons_castSucc, Fin.cons_succ]

/-- `List.ofFn` of a monotone function is a chain. -/
theorem isChain_ofFn : ∀ (k : ℕ) (ρ : Fin k → ℕ), Monotone ρ →
    List.IsChain (· ≤ ·) (List.ofFn ρ)
  | 0, ρ, _ => by simp
  | 1, ρ, _ => by simp
  | k + 2, ρ, hmono => by
      rw [List.ofFn_succ, List.ofFn_succ (f := fun i : Fin (k + 1) ↦ ρ i.succ)]
      refine List.isChain_cons_cons.mpr ⟨hmono (by simp), ?_⟩
      rw [← List.ofFn_succ (f := fun i : Fin (k + 1) ↦ ρ i.succ)]
      exact isChain_ofFn (k + 1) (fun i ↦ ρ i.succ) (fun i j hij ↦ hmono (by
        simp only [Fin.le_def, Fin.val_succ] at hij ⊢; omega))

/-- `0 :: List.ofFn ρ` is a chain, for monotone `ρ`. -/
theorem isChain_zero_cons_ofFn {k : ℕ} (ρ : Fin (k + 1) → ℕ) (hmono : Monotone ρ) :
    List.IsChain (· ≤ ·) (0 :: List.ofFn ρ) := by
  rw [List.ofFn_succ]
  refine List.isChain_cons_cons.mpr ⟨Nat.zero_le _, ?_⟩
  rw [← List.ofFn_succ]
  exact isChain_ofFn (k + 1) ρ hmono

end HJOA3
