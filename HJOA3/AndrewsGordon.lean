module

public import QSeriesLib.NumberTheory.QTheory.Basic
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology

/-!
# Warnaar's `A₂` Andrews–Gordon identities
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3.AndrewsGordon

/-- Warnaar's `A₂` quadratic form `n² - nm + m²`, in `ℕ`. -/
def quadExp (n m : ℕ) : ℕ := n ^ 2 + m ^ 2 - n * m

/-- `2nm ≤ n² + m²` in `ℕ`, so `quadExp` does not truncate. -/
theorem two_mul_le_sq_add_sq (n m : ℕ) : 2 * (n * m) ≤ n ^ 2 + m ^ 2 := by
  zify
  nlinarith [sq_nonneg ((n : ℤ) - m)]

theorem sq_add_sq_le_two_mul_quadExp (n m : ℕ) : n ^ 2 + m ^ 2 ≤ 2 * quadExp n m := by
  have h := two_mul_le_sq_add_sq n m
  rw [quadExp, Nat.mul_sub]
  omega

/-- A binder is bounded by twice any bound on its `quadExp`: `n ≤ n² ≤ 2 quadExp n m`. -/
theorem le_two_mul_quadExp_left (n m : ℕ) : n ≤ 2 * quadExp n m :=
  (Nat.le_self_pow two_ne_zero n).trans <|
    le_trans (Nat.le_add_right _ _) (sq_add_sq_le_two_mul_quadExp n m)

/-- `quadExp` is symmetric, which is why `le_two_mul_quadExp_left` suffices for both binders. -/
theorem quadExp_comm (n m : ℕ) : quadExp n m = quadExp m n := by
  rw [quadExp, quadExp, Nat.mul_comm]; ring_nf

/-- `1/(q)_n` in `ℤ⟦X⟧`, the outer factor of both identities. -/
noncomputable def qPochhammerSelfInv (n : ℕ) : ℤ⟦X⟧ := invOfUnit (X; X)_n 1

/-- Warnaar's `θ(x; q) = (x; q)_∞ (q/x; q)_∞` at `x = X ^ j`, with `X ^ M` in the base slot. -/
noncomputable def theta1 (M j : ℕ) : ℤ⟦X⟧ :=
  ((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ * ((X : ℤ⟦X⟧) ^ (M - j); (X : ℤ⟦X⟧) ^ M)_∞

/-- Warnaar's `θ(x, y, z; q)`, the product of the three one-argument thetas. -/
noncomputable def theta3 (M j₁ j₂ j₃ : ℕ) : ℤ⟦X⟧ := theta1 M j₁ * theta1 M j₂ * theta1 M j₃

/-- The right side shared by both identities: `(q^M; q^M)_∞² / (q)_∞²` times a theta triple. -/
noncomputable def rhs (M j₁ j₂ j₃ : ℕ) : ℤ⟦X⟧ :=
  ((X : ℤ⟦X⟧) ^ M; (X : ℤ⟦X⟧) ^ M)_∞ ^ 2 * invOfUnit ((X : ℤ⟦X⟧); (X : ℤ⟦X⟧))_∞ 1 ^ 2 *
    theta3 M j₁ j₂ j₃

/-- The summand of `(1.10)`'s left side at radii `n : Fin (k + 1) → ℕ` and `m : Fin k → ℕ`. -/
noncomputable def minusTerm (k : ℕ) (n : Fin (k + 1) → ℕ) (m : Fin k → ℕ) : ℤ⟦X⟧ :=
  let m' : Fin (k + 1) → ℕ := Fin.snoc m (2 * n (Fin.last k))
  X ^ (n (Fin.last k) ^ 2) * qPochhammerSelfInv (n 0) *
    ∏ i : Fin k,
      X ^ quadExp (n i.castSucc) (m' i.castSucc) *
        qChoose (X : ℤ⟦X⟧) (n i.castSucc) (n i.succ) *
        qChoose (X : ℤ⟦X⟧) (n i.castSucc - n i.succ + m' i.succ) (m' i.castSucc)

/-- The left side of `(1.10)` at `𝐤 = k + 1`: the sum of `minusTerm` over all radii and all `m`. -/
noncomputable def minusLHS (k : ℕ) : ℤ⟦X⟧ :=
  ∑' p : (Fin (k + 1) → ℕ) × (Fin k → ℕ), minusTerm k p.1 p.2

/--
The right side of `(1.10)` at `𝐤 = k + 1`: modulus `3𝐤 + 2`, and the theta triple `θ(q^𝐤,
q^{𝐤+1}, q^{𝐤+1})`.
-/
noncomputable def minusRHS (k : ℕ) : ℤ⟦X⟧ := rhs (3 * k + 5) (k + 1) (k + 2) (k + 2)

/-- Warnaar `(1.10)` at `𝐤 = k + 1`. -/
def Minus (k : ℕ) : Prop := minusLHS k = minusRHS k

/--
The summand of `(1.11)`'s left side at radii `n : Fin (k + 1) → ℕ` and `m : Fin (k + 1) → ℕ`.
-/
noncomputable def plusTerm (k : ℕ) (n m : Fin (k + 1) → ℕ) : ℤ⟦X⟧ :=
  qPochhammerSelfInv (n 0) * qChoose (X : ℤ⟦X⟧) (2 * n (Fin.last k)) (m (Fin.last k)) *
    (∏ i : Fin (k + 1), X ^ quadExp (n i) (m i)) *
    ∏ i : Fin k,
      qChoose (X : ℤ⟦X⟧) (n i.castSucc) (n i.succ) *
        qChoose (X : ℤ⟦X⟧) (n i.castSucc - n i.succ + m i.succ) (m i.castSucc)

/-- The left side of `(1.11)` at `𝐤 = k + 2`. -/
noncomputable def plusLHS (k : ℕ) : ℤ⟦X⟧ :=
  ∑' p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ), plusTerm k p.1 p.2

/-- The right side of `(1.11)` at `𝐤 = k + 2`: modulus `M = 3𝐤 + 1` and `θ(q^𝐤, q^𝐤, q^{𝐤+1})`. -/
noncomputable def plusRHS (k : ℕ) : ℤ⟦X⟧ := rhs (3 * k + 7) (k + 2) (k + 2) (k + 3)

/-- Warnaar `(1.11)` at `𝐤 = k + 2`. -/
def Plus (k : ℕ) : Prop := plusLHS k = plusRHS k

/-- `minusTerm` at `𝐤 = 2` is Warnaar's `(1.10)` summand at `𝐤 = 2`, on the chamber. -/
theorem minusTerm_one (n : Fin 2 → ℕ) (m : Fin 1 → ℕ) (h : n 1 ≤ n 0) :
    minusTerm 1 n m = X ^ (n 1 ^ 2) * qPochhammerSelfInv (n 0) *
      (X ^ quadExp (n 0) (m 0) * qChoose (X : ℤ⟦X⟧) (n 0) (n 1) *
        qChoose (X : ℤ⟦X⟧) (n 0 + n 1) (m 0)) := by
  have harith : n 0 - n 1 + 2 * n 1 = n 0 + n 1 := by omega
  rw [minusTerm, Fin.prod_univ_one, show (0 : Fin 1).succ = Fin.last 1 from rfl,
    Fin.snoc_castSucc, Fin.snoc_last, show (Fin.last 1 : Fin 2) = 1 from rfl, Fin.castSucc_zero,
    harith]

/-- Off the chamber, `(1.10)`'s summand vanishes. -/
theorem minusTerm_eq_zero_of_lt (k : ℕ) (n : Fin (k + 1) → ℕ) (m : Fin k → ℕ) (i : Fin k)
    (h : n i.castSucc < n i.succ) : minusTerm k n m = 0 := by
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
  rw [qChoose_eq_zero_of_lt (q := (X : ℤ⟦X⟧)) h]
  ring

/-- `plusTerm` at `𝐤 = 2` is Warnaar's `(1.11)` summand at `𝐤 = 2`. -/
theorem plusTerm_zero (n m : Fin 1 → ℕ) :
    plusTerm 0 n m = qPochhammerSelfInv (n 0) * qChoose (X : ℤ⟦X⟧) (2 * n 0) (m 0) *
      X ^ quadExp (n 0) (m 0) := by
  simp [plusTerm, Fin.last]

private theorem unbounded_of_finite_le {α : Type*} {e : α → ℕ} (h : ∀ d, {a | e a ≤ d}.Finite) :
    Filter.Unbounded e :=
  Filter.tendsto_atTop.mpr fun d ↦ Filter.eventually_cofinite.mpr <|
    (h d).subset fun _ ha ↦ le_of_not_ge ha

/-- A box in a finite product of copies of `ℕ` is finite. -/
private theorem finite_box (ι : Type*) [Finite ι] (d : ℕ) :
    (Set.univ.pi fun _ : ι ↦ Set.Iic d).Finite :=
  Set.Finite.pi fun _ ↦ Set.finite_Iic d

/-- The `q`-binomial part of `(1.10)`'s summand — everything except the power of `X`. -/
noncomputable def minusCoeff (k : ℕ) (n : Fin (k + 1) → ℕ) (m : Fin k → ℕ) : ℤ⟦X⟧ :=
  let m' : Fin (k + 1) → ℕ := Fin.snoc m (2 * n (Fin.last k))
  qPochhammerSelfInv (n 0) *
    ∏ i : Fin k,
      qChoose (X : ℤ⟦X⟧) (n i.castSucc) (n i.succ) *
        qChoose (X : ℤ⟦X⟧) (n i.castSucc - n i.succ + m' i.succ) (m' i.castSucc)

/-- The total power of `X` in `(1.10)`'s summand: `n_𝐤² + ∑_{i<𝐤-1} quadExp nᵢ mᵢ`. -/
def minusExp (k : ℕ) (n : Fin (k + 1) → ℕ) (m : Fin k → ℕ) : ℕ :=
  n (Fin.last k) ^ 2 + ∑ i : Fin k, quadExp (n i.castSucc) (m i)

/-- `(1.10)`'s summand equals its coefficient times `X` raised to `minusExp`. -/
theorem minusTerm_eq (k : ℕ) (n : Fin (k + 1) → ℕ) (m : Fin k → ℕ) :
    minusTerm k n m = minusCoeff k n m * X ^ minusExp k n m := by
  rw [minusTerm, minusCoeff, minusExp, pow_add]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Fin.snoc_castSucc]
  ring

/-- `(1.10)`'s exponent has finite sublevel sets. -/
theorem unbounded_minusExp (k : ℕ) :
    Filter.Unbounded fun p : (Fin (k + 1) → ℕ) × (Fin k → ℕ) ↦ minusExp k p.1 p.2 := by
  refine unbounded_of_finite_le fun d ↦
    ((finite_box (Fin (k + 1)) (2 * d)).prod (finite_box (Fin k) (2 * d))).subset ?_
  rintro ⟨n, m⟩ (hp : minusExp k n m ≤ d)
  have hterm : ∀ i : Fin k, quadExp (n i.castSucc) (m i) ≤ d := fun i ↦
    le_trans (le_trans (Finset.single_le_sum (f := fun i : Fin k ↦ quadExp (n i.castSucc) (m i))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)) hp
  have hlast : n (Fin.last k) ≤ d :=
    le_trans (le_trans (Nat.le_self_pow two_ne_zero _) (Nat.le_add_right _ _)) hp
  refine Set.mk_mem_prod (Set.mem_univ_pi.mpr fun j ↦ ?_) (Set.mem_univ_pi.mpr fun i ↦ ?_)
  · induction j using Fin.lastCases with
    | last => exact Set.mem_Iic.mpr (hlast.trans (Nat.le_mul_of_pos_left d two_pos))
    | cast i =>
      exact Set.mem_Iic.mpr <|
        (le_two_mul_quadExp_left _ _).trans (Nat.mul_le_mul_left 2 (hterm i))
  · refine Set.mem_Iic.mpr <| le_trans ?_ (Nat.mul_le_mul_left 2 (hterm i))
    exact quadExp_comm (n i.castSucc) (m i) ▸ le_two_mul_quadExp_left (m i) _

/-- `(1.10)`'s family is summable, so `minusLHS` is its genuine sum and not `tsum`'s junk value. -/
theorem summable_minusTerm (k : ℕ) :
    Summable fun p : (Fin (k + 1) → ℕ) × (Fin k → ℕ) ↦ minusTerm k p.1 p.2 := by
  simpa only [minusTerm_eq] using
    (unbounded_minusExp k).summable_mul_pow (f := fun p ↦ minusCoeff k p.1 p.2)

/-- `Minus k` says exactly that `(1.10)`'s left side converges to its right side. -/
theorem hasSum_minus_iff (k : ℕ) :
    HasSum (fun p : (Fin (k + 1) → ℕ) × (Fin k → ℕ) ↦ minusTerm k p.1 p.2) (minusRHS k) ↔
      Minus k :=
  (summable_minusTerm k).hasSum_iff

/-- The `q`-binomial part of `(1.11)`'s summand. -/
noncomputable def plusCoeff (k : ℕ) (n m : Fin (k + 1) → ℕ) : ℤ⟦X⟧ :=
  qPochhammerSelfInv (n 0) * qChoose (X : ℤ⟦X⟧) (2 * n (Fin.last k)) (m (Fin.last k)) *
    ∏ i : Fin k,
      qChoose (X : ℤ⟦X⟧) (n i.castSucc) (n i.succ) *
        qChoose (X : ℤ⟦X⟧) (n i.castSucc - n i.succ + m i.succ) (m i.castSucc)

/-- The total power of `X` in `(1.11)`'s summand. -/
def plusExp (k : ℕ) (n m : Fin (k + 1) → ℕ) : ℕ := ∑ i : Fin (k + 1), quadExp (n i) (m i)

/-- `(1.11)`'s summand equals its coefficient times `X` raised to `plusExp`. -/
theorem plusTerm_eq (k : ℕ) (n m : Fin (k + 1) → ℕ) :
    plusTerm k n m = plusCoeff k n m * X ^ plusExp k n m := by
  rw [plusTerm, plusCoeff, plusExp, Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib]
  ring

/-- `(1.11)`'s exponent has finite sublevel sets. -/
theorem unbounded_plusExp (k : ℕ) :
    Filter.Unbounded fun p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ) ↦ plusExp k p.1 p.2 := by
  refine unbounded_of_finite_le fun d ↦
    ((finite_box (Fin (k + 1)) (2 * d)).prod (finite_box (Fin (k + 1)) (2 * d))).subset ?_
  rintro ⟨n, m⟩ (hp : plusExp k n m ≤ d)
  have hterm : ∀ i : Fin (k + 1), quadExp (n i) (m i) ≤ d := fun i ↦
    le_trans (Finset.single_le_sum (f := fun i : Fin (k + 1) ↦ quadExp (n i) (m i))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)) hp
  refine Set.mk_mem_prod (Set.mem_univ_pi.mpr fun i ↦ ?_) (Set.mem_univ_pi.mpr fun i ↦ ?_)
  · exact Set.mem_Iic.mpr <|
      (le_two_mul_quadExp_left _ _).trans (Nat.mul_le_mul_left 2 (hterm i))
  · exact Set.mem_Iic.mpr <| (quadExp_comm (n i) (m i) ▸ le_two_mul_quadExp_left (m i) _).trans
      (Nat.mul_le_mul_left 2 (hterm i))

/-- `(1.11)`'s family is summable. -/
theorem summable_plusTerm (k : ℕ) :
    Summable fun p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ) ↦ plusTerm k p.1 p.2 := by
  simpa only [plusTerm_eq] using
    (unbounded_plusExp k).summable_mul_pow (f := fun p ↦ plusCoeff k p.1 p.2)

/-- `Plus k` says exactly that `(1.11)`'s left side converges to its right side. -/
theorem hasSum_plus_iff (k : ℕ) :
    HasSum (fun p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ) ↦ plusTerm k p.1 p.2) (plusRHS k) ↔
      Plus k :=
  (summable_plusTerm k).hasSum_iff

/-- Warnaar's Theorem 1.1, both halves, at every `𝐤` he claims them for. -/
def Theorem11 : Prop := (∀ k, Minus k) ∧ (∀ k, Plus k)

end HJOA3.AndrewsGordon
