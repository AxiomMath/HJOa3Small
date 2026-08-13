module

public import HJOA3.AndrewsGordon.Four

/-!
# Finite-support sums and antitone chains
-/

@[expose] public section

open Finset Polynomial PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJOA3.AndrewsGordon

/--
A `tsum` of terms with a common factor, supported on a finite set, is that factor times the
finite sum.
-/
theorem tsum_eq_mul_toSeries_finsum {ι : Type*} (F : ι → ℤ⟦X⟧) (f : ι → ℕ[X]) (C : ℤ⟦X⟧)
    (s : Finset ι) (hs : f.support ⊆ s) (hF : ∀ i, F i = C * toSeries (f i)) :
    ∑' i, F i = C * toSeries (∑ᶠ i, f i) := by
  have hzero : ∀ i ∉ s, f i = 0 := fun i hi ↦ by
    by_contra h
    exact hi (Finset.mem_coe.mp (hs (Function.mem_support.mpr h)))
  rw [finsum_eq_sum_of_support_subset _ hs, map_sum, Finset.mul_sum,
    tsum_eq_sum (s := s) fun i hi ↦ by rw [hF i, hzero i hi, map_zero, mul_zero]]
  exact Finset.sum_congr rfl fun i _ ↦ hF i

/-- A two-term decreasing chain is an antitone function on `Fin 2`. -/
theorem antitone_of_le (w : Fin 2 → ℕ) (hw : w 1 ≤ w 0) : Antitone w := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- A three-term decreasing chain is an antitone function on `Fin 3`. -/
theorem antitone_of_le₃ (w : Fin 3 → ℕ) (h₁ : w 1 ≤ w 0) (h₂ : w 2 ≤ w 1) : Antitone w := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  omega

end HJOA3.AndrewsGordon
