module

public import HJOA3.AndrewsGordon
public import HJOA3.ChargePochhammer

/-!
# Warnaar's product side is HJO's charge, at every modulus
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3.AndrewsGordon

/-- The residue class of `0` is charged nothing, written as `a + b` rather than as `0`. -/
theorem negR_add_self (a b : ℕ) : HJO.negR a b (a + b) = 0 := by
  have h : Int.bmod ((a : ℤ) * ((a + b : ℕ) : ℤ)) (a + b) = 0 := by
    rw [← Int.emod_bmod]
    simp
  rw [HJO.negR, h]
  simp

/--
The eight Pochhammer symbols in the numerator of `rhs M j₁ j₂ j₃`, as the list of their
numerator exponents: `M` twice from `(q^M; q^M)_∞²`, and `jᵢ` with `M - jᵢ` from each theta
factor.
-/
def rhsNumerator (M j₁ j₂ j₃ : ℕ) : List ℕ := [M, M, j₁, M - j₁, j₂, M - j₂, j₃, M - j₃]

/-- The cancellation behind both `q`-series comparisons, with no `q`-series in it. -/
theorem prod_pow_cancel {R : Type*} [CommMonoid R] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P p : ι → R) (hPp : ∀ k ∈ s, P k * p k = 1) (L : List ι) (hL : L.toFinset ⊆ s)
    (n : ℕ) (e : ι → ℕ) (hcount : ∀ k ∈ s, L.count k + e k = n) :
    (L.map P).prod * (∏ k ∈ s, p k) ^ n = ∏ k ∈ s, p k ^ e k := by
  rw [Finset.prod_list_map_count, prod_subset hL fun x _ hx ↦ by
      rw [List.count_eq_zero_of_not_mem (by simpa using hx), pow_zero],
    ← prod_pow, ← prod_mul_distrib]
  refine prod_congr rfl fun k hk ↦ ?_
  rw [← hcount k hk, pow_add, ← mul_assoc, ← mul_pow, hPp k hk, one_pow, one_mul]

/--
Warnaar's product side at modulus `M = a + b` is `HJO.charge a b`, whenever the exponents match
up.
-/
theorem rhs_eq_charge (a b M j₁ j₂ j₃ : ℕ) (hM : a + b = M) (hab : 0 < M)
    (hj₁ : j₁ ∈ Ico 1 M) (hj₂ : j₂ ∈ Ico 1 M) (hj₃ : j₃ ∈ Ico 1 M)
    (hcount : ∀ k ∈ Icc 1 M, (rhsNumerator M j₁ j₂ j₃).count k + HJO.negR a b k = 2) :
    rhs M j₁ j₂ j₃ = HJO.charge a b := by
  subst hM
  have hccP : ∀ k, k ≠ 0 →
      constantCoeff ((X : ℤ⟦X⟧) ^ k; (X : ℤ⟦X⟧) ^ (a + b))_∞ = 1 := fun k hk ↦
    constantCoeff_qPochhammerInf_pow (a + b) k hab hk
  have hPp : ∀ k ∈ Icc 1 (a + b), ((X : ℤ⟦X⟧) ^ k; (X : ℤ⟦X⟧) ^ (a + b))_∞ *
      invOfUnit ((X : ℤ⟦X⟧) ^ k; (X : ℤ⟦X⟧) ^ (a + b))_∞ 1 = 1 := fun k hk ↦
    mul_invOfUnit _ 1 (by rw [hccP k (by rw [mem_Icc] at hk; omega)]; rfl)
  have hIcc : Icc 1 (a + b) = Ico 1 (a + b + 1) := by ext x; simp
  have hrange : ∀ f : ℕ → ℤ⟦X⟧, f 0 = 1 → f (a + b) = 1 →
      ∏ k ∈ range (a + b), f k = ∏ k ∈ Icc 1 (a + b), f k := by
    intro f h0 hlast
    rw [range_eq_Ico, prod_eq_prod_Ico_succ_bot hab, h0, one_mul, hIcc,
      prod_Ico_succ_top hab, hlast, mul_one]
  have hcharge : HJO.charge a b = ∏ k ∈ Icc 1 (a + b),
      invOfUnit ((X : ℤ⟦X⟧) ^ k; (X : ℤ⟦X⟧) ^ (a + b))_∞ 1 ^ HJO.negR a b k := by
    rw [charge_eq_prod_qPochhammerInv a b hab,
      Fin.prod_univ_eq_prod_range (fun k ↦
        invOfUnit ((X : ℤ⟦X⟧) ^ k; (X : ℤ⟦X⟧) ^ (a + b))_∞ 1 ^ HJO.negR a b k) (a + b)]
    exact hrange _ (by simp [HJO.negR_zero]) (by simp [negR_add_self])
  have hinv : invOfUnit ((X : ℤ⟦X⟧); (X : ℤ⟦X⟧))_∞ 1 = ∏ k ∈ Icc 1 (a + b),
      invOfUnit ((X : ℤ⟦X⟧) ^ k; (X : ℤ⟦X⟧) ^ (a + b))_∞ 1 := by
    rw [qPochhammerInf_self_eq_prod_pow (a + b) hab.ne',
      invOfUnit_prod_of_constantCoeff_eq_one _ _ fun j _ ↦ hccP (j + 1) (Nat.succ_ne_zero j),
      hIcc, prod_Ico_eq_prod_range]
    exact prod_congr rfl fun i _ ↦ by rw [add_comm]
  have hsub : (rhsNumerator (a + b) j₁ j₂ j₃).toFinset ⊆ Icc 1 (a + b) := by
    rw [mem_Ico] at hj₁ hj₂ hj₃
    intro x hx
    simp only [rhsNumerator, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [mem_Icc]
    rcases hx with h | h | h | h | h | h | h | h <;> subst h <;> omega
  have hnum : ((rhsNumerator (a + b) j₁ j₂ j₃).map fun k ↦
        ((X : ℤ⟦X⟧) ^ k; (X : ℤ⟦X⟧) ^ (a + b))_∞).prod
      = ((X : ℤ⟦X⟧) ^ (a + b); (X : ℤ⟦X⟧) ^ (a + b))_∞ ^ 2 * theta3 (a + b) j₁ j₂ j₃ := by
    simp only [rhsNumerator, theta3, theta1, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil]
    ring
  rw [rhs, hinv, mul_right_comm, ← hnum, hcharge]
  exact prod_pow_cancel _ _ _ hPp _ hsub _ _ hcount

end HJOA3.AndrewsGordon
