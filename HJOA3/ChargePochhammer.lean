module

public import QSeriesLib.NumberTheory.QTheory.StrongNonarchimedean
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public import HJOA3.ChargeResidue
public import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-!
# `HJO.charge` as a finite product of `q`-Pochhammer inverses
-/

@[expose] public section

open Filter Finset PowerSeries Topology
open scoped PowerSeries.DiscreteTopology QTheory

/-- A Pochhammer symbol at a power base is the product along a residue class. -/
theorem qPochhammerInf_pow_eq_tprod_class (M j : ℕ) (hM : M ≠ 0) :
    ((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ = ∏' t : ℕ, ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) := by
  have hnil : IsTopologicallyNilpotent ((X : ℤ⟦X⟧) ^ M) := by
    simp [hM]
  rw [qPochhammerInf_eq_tprod hnil]
  exact tprod_congr fun t ↦ by rw [← pow_mul, ← pow_add, Nat.add_comm j (M * t)]

/-- `(q)_∞` splits by residue modulo `M`: `(X; X)_∞ = ∏_{j = 1}^{M} (X ^ j; X ^ M)_∞`. -/
theorem qPochhammerInf_self_eq_prod_pow (M : ℕ) (hM : M ≠ 0) :
    ((X : ℤ⟦X⟧); (X : ℤ⟦X⟧))_∞ = ∏ j ∈ range M, ((X : ℤ⟦X⟧) ^ (j + 1); (X : ℤ⟦X⟧) ^ M)_∞ := by
  rw [qPochhammerInf_eq_prod_range (a := (X : ℤ⟦X⟧)) (q := (X : ℤ⟦X⟧)) (m := M) hM
    DiscreteTopology.isTopologicallyNilpotent_X]
  exact prod_congr rfl fun j _ ↦ by rw [← pow_succ']

/--
The factors of that product are multipliable — the criterion applies because `(1 - X ^ (M t +
j))` differs from `1` in order `M t + j ≥ t`.
-/
theorem multipliable_one_sub_X_pow_class (M j : ℕ) (hM : 0 < M) :
    Multipliable fun t : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (M * t + j) := by
  have h : Multipliable (1 - (fun t : ℕ ↦ (X : ℤ⟦X⟧) ^ (M * t + j)) ·) := by
    refine WithPiTopology.multipliable_one_sub_of_tendsto_order ?_
    simp only [order_X_pow]
    exact WithTop.tendsto_coe_atTop.comp <| tendsto_atTop_mono
      (fun t ↦ (Nat.le_mul_of_pos_left t hM).trans (Nat.le_add_right _ j)) tendsto_id
  simpa only [Pi.sub_apply, Pi.one_apply] using h

/-- The inverse factors along a residue class are multipliable. -/
theorem multipliable_invOfUnit_one_sub_X_pow_class (M j : ℕ) (hM : 0 < M) :
    Multipliable fun t : ℕ ↦ invOfUnit ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) 1 := by
  simpa using multipliable_chargeFactor_class (fun _ ↦ 1) M j hM

/--
A Pochhammer symbol at a power base is a unit, for a nonzero numerator exponent: its constant
coefficient is the product of the factors' constant coefficients, all `1`.
-/
theorem constantCoeff_qPochhammerInf_pow (M j : ℕ) (hM : 0 < M) (hj : j ≠ 0) :
    constantCoeff ((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ = 1 := by
  rw [qPochhammerInf_pow_eq_tprod_class M j hM.ne',
    (multipliable_one_sub_X_pow_class M j hM).map_tprod constantCoeff
      (WithPiTopology.continuous_constantCoeff ℤ)]
  refine Eq.trans (tprod_congr fun t ↦ ?_) tprod_one
  simp [hj]

/-- The class product of the inverse factors is the inverse of the Pochhammer symbol. -/
theorem tprod_invOfUnit_one_sub_X_pow_class (M j : ℕ) (hM : 0 < M) (hj : j ≠ 0) :
    ∏' t : ℕ, invOfUnit ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) 1
      = invOfUnit ((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ 1 := by
  have hccg : ∀ t : ℕ, constantCoeff ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) = 1 := fun t ↦ by
    simp [hj]
  have hmu := multipliable_invOfUnit_one_sub_X_pow_class M j hM
  have hccA : constantCoeff ((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ = 1 :=
    constantCoeff_qPochhammerInf_pow M j hM hj
  have hprod : (∏' t : ℕ, invOfUnit ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) 1) *
      ((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ = 1 := by
    rw [qPochhammerInf_pow_eq_tprod_class M j hM.ne',
      ← hmu.tprod_mul (multipliable_one_sub_X_pow_class M j hM)]
    exact Eq.trans (tprod_congr fun t ↦ invOfUnit_mul _ 1 (by rw [hccg t]; rfl)) tprod_one
  calc ∏' t : ℕ, invOfUnit ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) 1
      = (∏' t : ℕ, invOfUnit ((1 : ℤ⟦X⟧) - X ^ (M * t + j)) 1) *
          (((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ * invOfUnit _ 1) := by
        rw [mul_invOfUnit _ 1 (by rw [hccA]; rfl), mul_one]
    _ = 1 * invOfUnit ((X : ℤ⟦X⟧) ^ j; (X : ℤ⟦X⟧) ^ M)_∞ 1 := by rw [← mul_assoc, hprod]
    _ = _ := one_mul _

section InvOfUnit

variable {R : Type*} [CommRing R]

/-- `invOfUnit` is multiplicative on series with constant coefficient `1`. -/
theorem invOfUnit_mul_of_constantCoeff_eq_one (f g : R⟦X⟧)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    invOfUnit (f * g) 1 = invOfUnit f 1 * invOfUnit g 1 := by
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, one_mul]
  have key : f * g * (invOfUnit f 1 * invOfUnit g 1) = 1 := by
    rw [show f * g * (invOfUnit f 1 * invOfUnit g 1)
        = f * invOfUnit f 1 * (g * invOfUnit g 1) by ring,
      mul_invOfUnit f 1 (by rw [hf]; rfl), mul_invOfUnit g 1 (by rw [hg]; rfl), one_mul]
  calc invOfUnit (f * g) 1
      = invOfUnit (f * g) 1 * (f * g * (invOfUnit f 1 * invOfUnit g 1)) := by rw [key, mul_one]
    _ = invOfUnit (f * g) 1 * (f * g) * (invOfUnit f 1 * invOfUnit g 1) := by ring
    _ = _ := by rw [invOfUnit_mul _ 1 (by rw [hfg]; rfl), one_mul]

/-- A finite product of series with constant coefficient `1` again has constant coefficient `1`. -/
theorem constantCoeff_prod_eq_one {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) : constantCoeff (∏ i ∈ s, f i) = 1 := by
  rw [map_prod]
  exact prod_eq_one hf

/-- `invOfUnit` distributes over finite products with constant coefficient `1`. -/
theorem invOfUnit_prod_of_constantCoeff_eq_one {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    invOfUnit (∏ i ∈ s, f i) 1 = ∏ i ∈ s, invOfUnit (f i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mul_invOfUnit (1 : R⟦X⟧) 1 (by simp)
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha,
      invOfUnit_mul_of_constantCoeff_eq_one _ _ (hf a (mem_insert_self a s))
        (constantCoeff_prod_eq_one s f fun i hi ↦ hf i (mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (mem_insert_of_mem hi)]

end InvOfUnit

/-- `HJO.charge` as a finite product of Pochhammer inverses. -/
theorem charge_eq_prod_qPochhammerInv (a b : ℕ) (hab : 0 < a + b) :
    HJO.charge a b = ∏ j : Fin (a + b),
      invOfUnit ((X : ℤ⟦X⟧) ^ (j : ℕ); (X : ℤ⟦X⟧) ^ (a + b))_∞ 1 ^ HJO.negR a b (j : ℕ) := by
  rw [charge_eq_prod_residue a b hab]
  refine prod_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne (j : ℕ) 0 with hj | hj
  · simp only [hj, HJO.negR_zero, pow_zero, tprod_one]
  · rw [(multipliable_invOfUnit_one_sub_X_pow_class _ _ hab).tprod_pow,
      tprod_invOfUnit_one_sub_X_pow_class _ _ hab hj]
