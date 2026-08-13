module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import QSeriesLib.Data.Fin.Tuple.Finset

/-!
# Regrouping a box sum by antidiagonals
-/

@[expose] public section

open Fin Finset Fintype

namespace HJOA3

/--
Regroup a sum over the box `[0, a] × [0, b]` as a sum over the antidiagonals of `0, …, N`,
provided the summand vanishes off the box and the box fits (`a + b ≤ N`).
-/
theorem sum_box_eq_sum_antidiagonal {M : Type*} [AddCommMonoid M] {a b N : ℕ}
    (hab : a + b ≤ N) (f : ℕ → ℕ → M)
    (hf : ∀ p : ℕ × ℕ, ¬(p.1 ≤ a ∧ p.2 ≤ b) → f p.1 p.2 = 0) :
    ∑ n₂ ∈ range (b + 1), ∑ n₁ ∈ range (a + 1), f n₁ n₂ =
    ∑ m ∈ range (N + 1), ∑ p ∈ Finset.antidiagonal m, f p.1 p.2 := by
  classical
  have hmaps : ∀ p ∈ range (a + 1) ×ˢ range (b + 1), p.1 + p.2 ∈ range (N + 1) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hp ⊢
    omega
  rw [Finset.sum_comm, ← Finset.sum_product',
    ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ ↦ p.1 + p.2) hmaps]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  refine Finset.sum_subset (fun p hp ↦ ?_) fun p hp hps ↦ hf p ?_
  · simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢
    exact hp.2
  · simp only [Finset.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
      hp, and_true, not_and] at hps
    tauto

/--
The `k`-variable version of `sum_box_eq_sum_antidiagonal`: regroup a sum over a box `∏ i, [0,
bd i]` in `ℕ ^ k` as a sum over the antidiagonal tuples of `0, …, N`, provided the summand
vanishes off the box and the box fits (`∑ i, bd i ≤ N`).
-/
theorem sum_box_eq_sum_antidiagonalTuple {M : Type*} [AddCommMonoid M] {k N : ℕ}
    (bd : Fin k → ℕ) (hbd : ∑ i, bd i ≤ N) (f : (Fin k → ℕ) → M)
    (hf : ∀ v : Fin k → ℕ, ¬(∀ i, v i ≤ bd i) → f v = 0) :
    ∑ v ∈ Fintype.piFinset fun i ↦ range (bd i + 1), f v =
    ∑ m ∈ range (N + 1), ∑ v ∈ Nat.antidiagonalTuple k m, f v := by
  classical
  have hmaps : ∀ v ∈ Fintype.piFinset fun i ↦ range (bd i + 1),
      ∑ i, v i ∈ range (N + 1) := by
    intro v hv
    simp only [Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] at hv ⊢
    exact le_trans (Finset.sum_le_sum fun i _ ↦ hv i) hbd
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v : Fin k → ℕ ↦ ∑ i, v i) hmaps]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  refine Finset.sum_subset (fun v hv ↦ ?_) fun v hv hvs ↦ hf v ?_
  · simp only [Finset.mem_filter, Nat.mem_antidiagonalTuple] at hv ⊢
    exact hv.2
  · simp only [Nat.mem_antidiagonalTuple] at hv
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff,
      hv, and_true] at hvs
    tauto

/--
Expand a `Fintype.piFinset` sum over `Fin 3` into three nested sums, with the tuple written in
`![x, y, z]` form.
-/
theorem sum_piFinset_fin_three {M : Type*} [AddCommMonoid M] {γ : Type*}
    (s : Fin 3 → Finset γ) (f : (Fin 3 → γ) → M) :
    ∑ v ∈ Fintype.piFinset s, f v = ∑ x ∈ s 0, ∑ y ∈ s 1, ∑ z ∈ s 2, f ![x, y, z] := by
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [sum_piFinset_fin_zero]
  congr 1

/-- The `Fin 4` case of `sum_piFinset_fin_three`, with the tuple written `![w, x, y, z]`. -/
theorem sum_piFinset_fin_four {M : Type*} [AddCommMonoid M] {γ : Type*}
    (s : Fin 4 → Finset γ) (f : (Fin 4 → γ) → M) :
    ∑ v ∈ Fintype.piFinset s, f v =
      ∑ w ∈ s 0, ∑ x ∈ s 1, ∑ y ∈ s 2, ∑ z ∈ s 3, f ![w, x, y, z] := by
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [sum_piFinset_fin_zero]
  congr 1

/-- The `Fin 2` case of `sum_piFinset_fin_three`, with the tuple written `![x, y]`. -/
theorem sum_piFinset_fin_two {M : Type*} [AddCommMonoid M] {γ : Type*}
    (s : Fin 2 → Finset γ) (f : (Fin 2 → γ) → M) :
    ∑ v ∈ Fintype.piFinset s, f v = ∑ x ∈ s 0, ∑ y ∈ s 1, f ![x, y] := by
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [sum_piFinset_fin_succ]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [sum_piFinset_fin_zero]
  congr 1

/--
Shift a `range` sum by `n` and extend it back down to `0`, when the summand vanishes below `n`.
-/
theorem sum_range_shift_of_vanish {M : Type*} [AddCommMonoid M] {n N : ℕ} (hn : n ≤ N)
    (G : ℕ → M) (h : ∀ a < n, G a = 0) :
    ∑ d ∈ range (N - n + 1), G (n + d) = ∑ a ∈ range (N + 1), G a := by
  classical
  have hsub : Finset.Ico n (N + 1) ⊆ range (N + 1) := by
    intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  have hvan : ∀ a ∈ range (N + 1), a ∉ Finset.Ico n (N + 1) → G a = 0 := by
    intro a ha hai
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico, not_and, not_lt] at hai
    exact h a (by omega)
  rw [← Finset.sum_subset hsub hvan, Finset.sum_Ico_eq_sum_range,
    show N + 1 - n = N - n + 1 from by omega]

/-- Shrink a `range` sum from `[0, N]` to `[0, m]` when the summand vanishes above `m`. -/
theorem sum_range_shrink {M : Type*} [AddCommMonoid M] {m N : ℕ} (hmN : m ≤ N) (G : ℕ → M)
    (h : ∀ i, m < i → G i = 0) :
    ∑ i ∈ range (N + 1), G i = ∑ i ∈ range (m + 1), G i :=
  (Finset.sum_subset (s₁ := range (m + 1)) (s₂ := range (N + 1))
    (fun x hx ↦ Finset.mem_range.mpr (by
      simp only [Finset.mem_range] at hx
      omega))
    fun i _ hi ↦ h i (by
      simp only [Finset.mem_range, not_lt] at hi
      omega)).symm

/--
A quadruple sum whose summand splits as `f a b * g c d` factors as a product of two double
sums.
-/
theorem sum_sum_mul_sum_sum {M : Type*} [CommSemiring M] (s t u v : Finset ℕ)
    (f g : ℕ → ℕ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b * g c d =
      (∑ a ∈ s, ∑ b ∈ t, f a b) * ∑ c ∈ u, ∑ d ∈ v, g c d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.mul_sum]

/--
A `Fintype.piFinset` sum with *constant* bounds is invariant under permuting the coordinates.
-/
theorem sum_piFinset_const_comp {γ : Type*} {M : Type*} [AddCommMonoid M]
    {k : ℕ} (t : Finset γ) (e : Equiv.Perm (Fin k)) (F : (Fin k → γ) → M) :
    ∑ v ∈ Fintype.piFinset fun _ ↦ t, F v =
      ∑ v ∈ Fintype.piFinset fun _ ↦ t, F (v ∘ e) := by
  refine Finset.sum_equiv (Equiv.arrowCongr e (Equiv.refl γ)) (fun v ↦ ?_) (fun v _ ↦ ?_)
  · simp only [Fintype.mem_piFinset, Equiv.arrowCongr_apply, Equiv.coe_refl,
      Function.comp_apply, id_eq]
    exact ⟨fun h i ↦ h _, fun h i ↦ by simpa using h (e i)⟩
  · congr 1
    funext i
    simp

/--
Split a sum over a `Fin (2 * k)` box whose summand factors through the first `k` and the last
`k` coordinates.
-/
theorem sum_piFinset_split {M : Type*} [CommSemiring M] {k : ℕ}
    (s : Fin (2 * k) → Finset ℕ) (F G : (Fin k → ℕ) → M) :
    ∑ v ∈ Fintype.piFinset s,
        F (fun i : Fin k ↦ v ⟨i.val, by omega⟩) * G (fun i : Fin k ↦ v ⟨k + i.val, by omega⟩) =
      (∑ x ∈ Fintype.piFinset (fun i : Fin k ↦ s ⟨i.val, by omega⟩), F x) *
      (∑ y ∈ Fintype.piFinset (fun i : Fin k ↦ s ⟨k + i.val, by omega⟩), G y) := by
  classical
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij'
    (i := fun v ↦ (fun i : Fin k ↦ v ⟨i.val, by omega⟩, fun i : Fin k ↦ v ⟨k + i.val, by omega⟩))
    (j := fun p ↦ fun j : Fin (2 * k) ↦
      if h : j.val < k then p.1 ⟨j.val, h⟩ else p.2 ⟨j.val - k, by omega⟩)
    ?hi ?hj ?left ?right ?h
  · intro v hv
    simp only [Fintype.mem_piFinset] at hv
    simp only [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨fun i ↦ hv _, fun i ↦ hv _⟩
  · intro p hp
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hp
    simp only [Fintype.mem_piFinset]
    intro j
    split_ifs with hj
    · have h1 := hp.1 ⟨j.val, hj⟩
      have hidx : (⟨j.val, by omega⟩ : Fin (2 * k)) = j := Fin.val_injective (by simp)
      rwa [hidx] at h1
    · have h2 := hp.2 ⟨j.val - k, by omega⟩
      have hidx : (⟨k + (j.val - k), by omega⟩ : Fin (2 * k)) = j := by
        apply Fin.val_injective
        change k + (j.val - k) = j.val
        omega
      rwa [hidx] at h2
  · intro v _
    funext j
    split_ifs with hj
    · rfl
    · change v ⟨k + (j.val - k), by omega⟩ = v j
      congr 1
      apply Fin.val_injective
      change k + (j.val - k) = j.val
      omega
  · intro p _
    ext i <;> simp
  · intro v _
    rfl

/-- Enlarge a `piFinset` box coordinatewise, when the summand vanishes outside the smaller one. -/
theorem sum_piFinset_enlarge {M : Type*} [AddCommMonoid M] {k : ℕ} (s t : Fin k → Finset ℕ)
    (hst : ∀ i, s i ⊆ t i) (f : (Fin k → ℕ) → M)
    (hf : ∀ v, (∃ i, v i ∉ s i) → f v = 0) :
    ∑ v ∈ Fintype.piFinset s, f v = ∑ v ∈ Fintype.piFinset t, f v := by
  refine Finset.sum_subset (Fintype.piFinset_subset _ _ hst) fun v _ hv ↦ hf v ?_
  simp only [Fintype.mem_piFinset, not_forall] at hv
  exact hv

end HJOA3
