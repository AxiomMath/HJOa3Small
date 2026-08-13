module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Regrouping an infinite product over `ℕ` by residue class
-/

@[expose] public section

open Finset

/-- Residue regrouping for infinite products. -/
theorem tprod_nat_eq_prod_residue {α : Type*} [CommMonoid α] [TopologicalSpace α]
    [T3Space α] [ContinuousMul α] {M : ℕ} [NeZero M] {f : ℕ → α}
    (hf : Multipliable f) (hres : ∀ j : Fin M, Multipliable fun t : ℕ ↦ f (M * t + j)) :
    ∏' n : ℕ, f n = ∏ j : Fin M, ∏' t : ℕ, f (M * t + j) := by
  set e : Fin M × ℕ ≃ ℕ := (Equiv.prodComm (Fin M) ℕ).trans (Nat.divModEquiv M).symm with he
  have key (j : Fin M) (t : ℕ) : f (e (j, t)) = f (M * t + j) := by rw [he]; simp [Nat.mul_comm]
  have hcomp : Multipliable fun p : Fin M × ℕ ↦ f (e p) := e.multipliable_iff.mpr hf
  rw [← e.tprod_eq f, hcomp.tprod_prod' fun j ↦ (hres j).congr fun t ↦ (key j t).symm,
    tprod_fintype]
  exact prod_congr rfl fun j _ ↦ tprod_congr (key j)
