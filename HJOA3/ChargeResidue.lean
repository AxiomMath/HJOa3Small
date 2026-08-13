module

public import QSeriesLib.NumberTheory.HJO.Defs
public import QSeriesLib.RingTheory.PowerSeries.PiTopology
public import HJOA3.NegR
public import HJOA3.TprodResidue
public import Mathlib.Topology.Order.WithTop

/-!
# `HJO.charge` as a finite product over residue classes
-/

@[expose] public section

open Finset Filter PowerSeries Topology
open scoped PowerSeries.DiscreteTopology QTheory

section Order

variable {R : Type*} [CommRing R]

/-- Inverting does not move a series closer to `1`. -/
theorem le_order_invOfUnit_sub_one (f : R⟦X⟧) (u : Rˣ) (h : constantCoeff f = u) :
    (f - 1).order ≤ (invOfUnit f u - 1).order := by
  have key : invOfUnit f u - 1 = (1 - f) * invOfUnit f u := by
    rw [sub_mul, one_mul, mul_invOfUnit f u h]
  calc (f - 1).order = (1 - f).order := by rw [← order_neg (f - 1), neg_sub]
    _ ≤ (1 - f).order + (invOfUnit f u).order := le_self_add
    _ ≤ ((1 - f) * invOfUnit f u).order := le_order_mul _ _
    _ = (invOfUnit f u - 1).order := by rw [key]

/-- Raising to a power does not move a series closer to `1`. -/
theorem le_order_pow_sub_one (f : R⟦X⟧) (e : ℕ) : (f - 1).order ≤ (f ^ e - 1).order := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [show f ^ (e + 1) - 1 = f * (f ^ e - 1) + (f - 1) by ring]
    exact le_trans (le_min (ih.trans (le_add_self.trans (le_order_mul f _))) le_rfl)
      (min_order_le_order_add _ _)

end Order

/--
The `n`-th factor of `HJO.charge` differs from `1` to order at least `n`, whatever exponent it
carries.
-/
theorem le_order_chargeFactor_sub_one (e n : ℕ) :
    (n : ℕ∞) ≤ (invOfUnit ((1 : ℤ⟦X⟧) - X ^ n) 1 ^ e - 1).order := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  have hc : constantCoeff ((1 : ℤ⟦X⟧) - X ^ n) = 1 := by simp [hn.ne']
  calc (n : ℕ∞) = ((1 : ℤ⟦X⟧) - X ^ n - 1).order := by
        rw [show (1 : ℤ⟦X⟧) - X ^ n - 1 = -(X ^ n) by ring, order_neg, order_X_pow]
    _ ≤ (invOfUnit ((1 : ℤ⟦X⟧) - X ^ n) 1 - 1).order := le_order_invOfUnit_sub_one _ 1 hc
    _ ≤ _ := le_order_pow_sub_one _ e

/--
The family under `HJO.charge`'s `∏'` is multipliable: its `n`-th factor is within order `n` of
`1`, and `n → ∞`.
-/
theorem multipliable_chargeFactor (e : ℕ → ℕ) :
    Multipliable fun n : ℕ ↦ invOfUnit ((1 : ℤ⟦X⟧) - X ^ n) 1 ^ e n :=
  WithPiTopology.multipliable_of_tendsto_order_sub_one <|
    tendsto_nhds_top_mono' WithTop.tendsto_coe_atTop fun n ↦ le_order_chargeFactor_sub_one _ n

/-- Each residue-class family of charge factors is multipliable. -/
theorem multipliable_chargeFactor_class (e : ℕ → ℕ) (M j : ℕ) (hM : 0 < M) :
    Multipliable fun t : ℕ ↦ invOfUnit ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) 1 ^ e t := by
  refine WithPiTopology.multipliable_of_tendsto_order_sub_one <|
    tendsto_nhds_top_mono' WithTop.tendsto_coe_atTop fun t ↦ ?_
  refine le_trans ?_ (le_order_chargeFactor_sub_one _ (M * t + j))
  exact Nat.cast_le.mpr <| Nat.le_trans (Nat.le_mul_of_pos_left t hM) (Nat.le_add_right _ j)

/--
`HJO.charge` is a finite product over residue classes, each contributing the constant power its
residue carries.
-/
theorem charge_eq_prod_residue (a b : ℕ) (hab : 0 < a + b) :
    HJO.charge a b = ∏ j : Fin (a + b), ∏' t : ℕ,
      invOfUnit ((1 : ℤ⟦X⟧) - X ^ ((a + b) * t + (j : ℕ))) 1 ^ HJO.negR a b (j : ℕ) := by
  have : NeZero (a + b) := ⟨hab.ne'⟩
  rw [HJO.charge, tprod_nat_eq_prod_residue (multipliable_chargeFactor (HJO.negR a b))
    fun j ↦ multipliable_chargeFactor_class _ _ _ hab]
  exact prod_congr rfl fun j _ ↦ tprod_congr fun t ↦ by rw [HJO.negR_mul_add]
