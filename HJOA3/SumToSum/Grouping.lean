module

public import QSeriesLib.NumberTheory.QTheory.Basic
public import QSeriesLib.NumberTheory.QTheory.Vandermonde
public import HJOA3.SumToSum.Box

/-!
# Grouping a `q`-Vandermonde box sum by the sum of its coordinates
-/

@[expose] public section

open Finset

namespace HJOA3

/-- Grouping a `q`-Vandermonde box sum by `∑ i, v i`. -/
theorem sum_box_weighted {R : Type*} [CommSemiring R] (q : R) {k : ℕ} (n : Fin k → ℕ)
    (g : ℕ → R) :
    ∑ v ∈ Fintype.piFinset fun i ↦ range (n i + 1),
      (q ^ (∑ i : Fin k, ∑ j : Fin k with i < j, (n i - v i) * v j) *
        ∏ i : Fin k, qChoose q (n i) (v i)) * g (∑ i, v i) =
    ∑ m ∈ range ((∑ i, n i) + 1), qChoose q (∑ i, n i) m * g m := by
  classical
  rw [sum_box_eq_sum_antidiagonalTuple n le_rfl _ fun v hv ↦ ?_]
  · refine Finset.sum_congr rfl fun m _ ↦ ?_
    have hfib : ∀ v ∈ Nat.antidiagonalTuple k m,
        (q ^ (∑ i : Fin k, ∑ j : Fin k with i < j, (n i - v i) * v j) *
          ∏ i : Fin k, qChoose q (n i) (v i)) * g (∑ i, v i) =
        (q ^ (∑ i : Fin k, ∑ j : Fin k with i < j, (n i - v i) * v j) *
          ∏ i : Fin k, qChoose q (n i) (v i)) * g m := by
      intro v hv
      rw [Nat.mem_antidiagonalTuple] at hv
      rw [hv]
    rw [Finset.sum_congr rfl hfib, ← Finset.sum_mul, ← qChoose_sum]
  · obtain ⟨i, hi⟩ := not_forall.mp hv
    have : qChoose q (n i) (v i) = 0 := qChoose_eq_zero_of_lt (by omega)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) this]
    simp

end HJOA3
