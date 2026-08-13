module

public import Batteries.Data.List.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Flag straightening at `q = 1`
-/

@[expose] public section

open Finset

namespace HJOA3

/-- The binomial theorem as a sum of `choose` against a power: `∑ k, C(n, k) * c ^ k`. -/
theorem sum_range_choose_mul_pow (n c : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * c ^ k = (c + 1) ^ n := by
  rw [add_pow]
  exact (Finset.sum_congr rfl fun k _ ↦ by simp [mul_comm]).symm

/--
The binomial theorem with the power on the complementary index: `∑ k, C(n, k) * c ^ (n - k)`.
-/
theorem sum_range_choose_mul_pow_sub (n c : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * c ^ (n - k) = (c + 1) ^ n := by
  rw [add_comm c 1, add_pow]
  exact (Finset.sum_congr rfl fun k _ ↦ by simp [mul_comm]).symm

/--
The `x`-part of the left-hand side: the number of chains `X₁ ⊆ ⋯` of finite sets whose `j`-th
term is confined to a set of size the `j`-th entry of the ascending list of radii, starting
from a base of size `b`.
-/
def xChain : ℕ → List ℕ → ℕ
  | _, [] => 1
  | b, ρ :: ρs => ∑ d ∈ range (ρ - b + 1), (ρ - b).choose d * xChain (b + d) ρs

/--
The `y`-part of the left-hand side: the number of chains `Y₁ ⊆ ⋯ ⊆ Y_ℓ ⊆ T` with `T` of size
`s`.
-/
def yChain : ℕ → ℕ → ℕ
  | 0, _ => 1
  | ℓ + 1, s => ∑ y ∈ range (s + 1), s.choose y * yChain ℓ y

/--
The right-hand side: the iterated sum over `m`, recursing over the list of gaps, with `c` the
incoming summation variable.
-/
def mChain : ℕ → List ℕ → ℕ
  | _, [] => 1
  | c, g :: gs => ∑ m ∈ range (g + c + 1), (g + c).choose m * mChain m gs

/-- The list of consecutive differences of a list: `gaps [a, b, c] = [b - a, c - b]`. -/
def gaps : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | a :: b :: l => (b - a) :: gaps (b :: l)

@[simp] theorem xChain_nil (b : ℕ) : xChain b [] = 1 := rfl

theorem xChain_cons (b ρ : ℕ) (ρs : List ℕ) :
    xChain b (ρ :: ρs) = ∑ d ∈ range (ρ - b + 1), (ρ - b).choose d * xChain (b + d) ρs := rfl

@[simp] theorem yChain_zero (s : ℕ) : yChain 0 s = 1 := rfl

theorem yChain_succ (ℓ s : ℕ) :
    yChain (ℓ + 1) s = ∑ y ∈ range (s + 1), s.choose y * yChain ℓ y := rfl

@[simp] theorem mChain_nil (c : ℕ) : mChain c [] = 1 := rfl

theorem mChain_cons (c g : ℕ) (gs : List ℕ) :
    mChain c (g :: gs) = ∑ m ∈ range (g + c + 1), (g + c).choose m * mChain m gs := rfl

@[simp] theorem gaps_nil : gaps [] = [] := rfl

@[simp] theorem gaps_singleton (a : ℕ) : gaps [a] = [] := rfl

@[simp] theorem gaps_cons_cons (a b : ℕ) (l : List ℕ) :
    gaps (a :: b :: l) = (b - a) :: gaps (b :: l) := rfl

@[simp] theorem gaps_length (a : ℕ) (l : List ℕ) : (gaps (a :: l)).length = l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [ih]

/--
`yChain ℓ s = (ℓ + 1) ^ s`: each of the `s` elements of `T` independently chooses the least
index at which it appears, or none at all.
-/
theorem yChain_eq_pow (ℓ s : ℕ) : yChain ℓ s = (ℓ + 1) ^ s := by
  induction ℓ generalizing s with
  | zero => simp
  | succ ℓ ih => simp only [yChain_succ, ih, sum_range_choose_mul_pow]

@[simp] theorem yChain_zero_right (ℓ : ℕ) : yChain ℓ 0 = 1 := by simp [yChain_eq_pow]

/--
The one-step recurrence for `xChain`: peeling the smallest radius off the front multiplies by
`(length + 2) ^ (ρ - b)`.
-/
theorem xChain_cons_eq :
    ∀ (ρs : List ℕ) (b ρ : ℕ), List.IsChain (· ≤ ·) (b :: ρ :: ρs) →
      xChain b (ρ :: ρs) = (ρs.length + 2) ^ (ρ - b) * xChain ρ ρs
  | [], b, ρ, _ => by simp [xChain_cons, Nat.sum_range_choose]
  | ρ' :: ρs', b, ρ, h => by
      obtain ⟨hbρ, h2⟩ := List.isChain_cons_cons.mp h
      obtain ⟨hρρ', hchain⟩ := List.isChain_cons_cons.mp h2
      have key : ∀ d ∈ range (ρ - b + 1),
          (ρ - b).choose d * xChain (b + d) (ρ' :: ρs') =
            ((ρ - b).choose d * (ρs'.length + 2) ^ (ρ - b - d)) *
              ((ρs'.length + 2) ^ (ρ' - ρ) * xChain ρ' ρs') := by
        intro d hd
        have hd' : d ≤ ρ - b := by simpa [Nat.lt_succ_iff] using hd
        rw [xChain_cons_eq ρs' (b + d) ρ' (List.isChain_cons_cons.mpr ⟨by omega, hchain⟩),
          show ρ' - (b + d) = ρ - b - d + (ρ' - ρ) by omega, pow_add]
        ring
      rw [xChain_cons, Finset.sum_congr rfl key, ← Finset.sum_mul,
        sum_range_choose_mul_pow_sub,
        xChain_cons_eq ρs' ρ ρ' (List.isChain_cons_cons.mpr ⟨hρρ', hchain⟩)]
      simp only [List.length_cons]

/-- The one-step recurrence for `mChain`. -/
theorem mChain_cons_eq :
    ∀ (gs : List ℕ) (c g : ℕ), mChain c (g :: gs) = (gs.length + 2) ^ (g + c) * mChain 0 gs
  | [], c, g => by simp [mChain_cons, Nat.sum_range_choose]
  | g' :: gs', c, g => by
      have key : ∀ m ∈ range (g + c + 1),
          (g + c).choose m * mChain m (g' :: gs') =
            ((g + c).choose m * (gs'.length + 2) ^ m) *
              ((gs'.length + 2) ^ g' * mChain 0 gs') := by
        intro m _
        rw [mChain_cons_eq gs' m g', pow_add]
        ring
      rw [mChain_cons, Finset.sum_congr rfl key, ← Finset.sum_mul, sum_range_choose_mul_pow,
        mChain_cons_eq gs' 0 g']
      simp only [List.length_cons, Nat.add_zero]

/-- Flag straightening at `q = 1` (Lemma 4.2, transfer-matrix form). -/
theorem xChain_mul_yChain_eq_mChain :
    ∀ (ρs : List ℕ) (b ρ s : ℕ), List.IsChain (· ≤ ·) (b :: ρ :: ρs) →
      xChain b (ρ :: ρs) * yChain (ρs.length + 1) s =
        mChain 0 ((ρ - b + s) :: gaps (ρ :: ρs))
  | [], b, ρ, s, h => by
      rw [xChain_cons_eq [] b ρ h, gaps_singleton, mChain_cons_eq [] 0 (ρ - b + s)]
      simp [yChain_eq_pow, pow_add]
  | ρ' :: ρs', b, ρ, s, h => by
      obtain ⟨hbρ, h2⟩ := List.isChain_cons_cons.mp h
      obtain ⟨hρρ', hchain⟩ := List.isChain_cons_cons.mp h2
      have ih : xChain ρ (ρ' :: ρs') = mChain 0 ((ρ' - ρ) :: gaps (ρ' :: ρs')) := by
        simpa using
          xChain_mul_yChain_eq_mChain ρs' ρ ρ' 0 (List.isChain_cons_cons.mpr ⟨hρρ', hchain⟩)
      rw [xChain_cons_eq (ρ' :: ρs') b ρ h, gaps_cons_cons,
        mChain_cons_eq ((ρ' - ρ) :: gaps (ρ' :: ρs')) 0 (ρ - b + s), ih]
      simp only [List.length_cons, gaps_length, yChain_eq_pow, Nat.add_zero]
      ring

end HJOA3
