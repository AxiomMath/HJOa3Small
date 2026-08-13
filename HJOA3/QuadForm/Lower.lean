module

public import QSeriesLib.NumberTheory.HJO.PosDef
public import HJOA3.QuadForm.StarBound

/-!
# The quantitative lower bound on `HJO.Q 3 b`
-/

@[expose] public section

open Finset Matrix NumericalSemigroup QuadraticMap QuadraticForm

namespace HJOA3.QuadForm

/-- How `LinearEquiv.piCongrLeft` acts, for a constant family. -/
theorem piCongrLeft_apply_const {ι κ : Type*} (e : ι ≃ κ) (y : ι → ℤ) :
    LinearEquiv.piCongrLeft ℤ (fun _ : κ ↦ ℤ) e y = fun i ↦ y (e.symm i) := by
  apply (LinearEquiv.piCongrLeft ℤ (fun _ : κ ↦ ℤ) e).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext j
  simp [LinearEquiv.piCongrLeft]

/-- The singleton block dominates a quarter of its own square, slackly. -/
theorem sum_sq_le_four_mul_q1' (y : Fin 1 → ℤ) : ∑ j, y j ^ 2 ≤ 4 * HJO.q1 y := by
  have hy : y = ![y 0] := by ext i; fin_cases i; simp
  rw [hy]
  simpa using sq_le_four_mul_q1 (y 0)

/-- The one-edge block `q3001 = x² + y² + z² - xz` dominates a quarter of its own squared norm. -/
theorem sum_sq_le_four_mul_q3001' (y : Fin 3 → ℤ) : ∑ j, y j ^ 2 ≤ 4 * HJO.q3001 y := by
  have hy : y = ![y 0, y 1, y 2] := by ext i; fin_cases i <;> simp
  rw [hy]
  simpa [Fin.sum_univ_three] using sq_le_four_mul_q3001 (y 0) (y 1) (y 2)

/--
The two-edge block `q3011 = x² + y² + z² - xz - yz` dominates a quarter of its own squared
norm.
-/
theorem sum_sq_le_four_mul_q3011' (y : Fin 3 → ℤ) : ∑ j, y j ^ 2 ≤ 4 * HJO.q3011 y := by
  have hy : y = ![y 0, y 1, y 2] := by ext i; fin_cases i <;> simp
  rw [hy]
  simpa [Fin.sum_univ_three] using sq_le_four_mul_q3011 (y 0) (y 1) (y 2)

/-- `Q` dominates `qModified` on the nonnegative orthant. -/
theorem qModified_le_Q' (G : Finset ℕ) (a b : ℕ) {n : G → ℤ} (hn : 0 ≤ n) :
    HJO.qModified G a b n ≤ HJO.Q' G a b n := by
  have hU : ∀ x : ℤ, HJO.uModified a b x ≤ HJO.U a b x := HJO.uModified_le_U
  have hn' : ∀ i, (0 : ℤ) ≤ n i := hn
  rw [HJO.qModified, HJO.Q', HJO.qMatrix, Matrix.toQuadraticForm_eq_sum_sum,
    Matrix.toQuadraticForm_eq_sum_sum]
  refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
  simp only [Matrix.of_apply]
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (hU _) (mul_nonneg (hn' i) (hn' j))

/-- The bound passes from `qModified` to `Q'` on the nonnegative orthant. -/
theorem sum_sq_le_four_mul_Q'_of_qModified {G : Finset ℕ} {c : ℕ} {m : G → ℤ} (hm : 0 ≤ m)
    (h : ∑ i, m i ^ 2 ≤ 4 * HJO.qModified G 3 c m) : ∑ i, m i ^ 2 ≤ 4 * HJO.Q' G 3 c m :=
  h.trans (by linarith [qModified_le_Q' G 3 c hm])

namespace ThreeOne

open HJO.ThreeOne NumericalSemigroup.ThreeOne

/-- The block bound for `b = 3k + 1`. -/
theorem sum_sq_le_four_mul_qCompare (k : ℕ) (x : Fin (3 * k) → ℤ) :
    ∑ i, x i ^ 2 ≤ 4 * qCompare k x := by
  set e := LinearEquiv.piCongrLeft ℤ (fun _ : Fin k × Fin 3 ↦ ℤ) (indexEquiv k) with he
  obtain ⟨y, rfl⟩ := e.symm.surjective x
  have hlhs : ∑ i, (e.symm y) i ^ 2 = ∑ b : Fin k, ∑ j : Fin 3, y (b, j) ^ 2 := by
    have h1 : ∑ i, (e.symm y) i ^ 2 = ∑ p : Fin k × Fin 3, y p ^ 2 :=
      Fintype.sum_equiv (indexEquiv k) _ _ fun i ↦ by
        simp [he, LinearEquiv.piCongrLeft]
    rw [h1, Fintype.sum_prod_type]
  rw [hlhs, qCompare, QuadraticMap.comp_apply, pi_apply, mul_sum]
  refine sum_le_sum fun b _ ↦ ?_
  have hblock : ∀ j : Fin 3,
      ((LinearEquiv.piCongrLeft ℤ (fun _ ↦ ℤ) (indexEquiv k) ≪≫ₗ
        LinearEquiv.curry ℤ ℤ (Fin k) (Fin 3)).toLinearMap (e.symm y)) b j = y (b, j) := by
    intro j
    simp [he]
  simp_rw [← hblock, DFunLike.ite_apply]
  split_ifs
  · exact sum_sq_le_four_mul_q3001' _
  · exact sum_sq_le_four_mul_q3011' _

/-- The sum-of-squares bound for `qModified` in the `b = 3k + 1` case. -/
theorem sum_sq_le_four_mul_qModified (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℤ) :
    ∑ i, n i ^ 2 ≤ 4 * HJO.qModified (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) n := by
  obtain ⟨y, rfl⟩ :=
    (LinearEquiv.piCongrLeft ℤ (fun _ : (finspan {3, 3 * k + 1}).gaps ↦ ℤ)
      (gapsEquiv k)).surjective n
  have key := DFunLike.congr_fun (qModified_comp_eq_qCompare k) y
  rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe] at key
  rw [key]
  refine le_of_eq_of_le ?_ (sum_sq_le_four_mul_qCompare k y)
  exact (Fintype.sum_equiv (gapsEquiv k) _ _ fun j ↦ by
    simp only [piCongrLeft_apply_const, Equiv.symm_apply_apply]).symm

end ThreeOne

namespace ThreeTwo

open HJO.ThreeTwo NumericalSemigroup.ThreeTwo

/-- The block bound for `b = 3k + 2`. -/
theorem sum_sq_le_four_mul_qCompare (k : ℕ) (x : Fin (3 * k + 1) → ℤ) :
    ∑ i, x i ^ 2 ≤ 4 * qCompare k x := by
  set e := LinearEquiv.piCongrLeft ℤ
    (fun _ : (i : Fin (k + 1)) × Fin (invLength i) ↦ ℤ) (indexEquiv k) with he
  obtain ⟨y, rfl⟩ := e.symm.surjective x
  have hlhs : ∑ i, (e.symm y) i ^ 2 =
      ∑ b : Fin (k + 1), ∑ j : Fin (invLength b), y ⟨b, j⟩ ^ 2 := by
    have h1 : ∑ i, (e.symm y) i ^ 2 = ∑ p : (i : Fin (k + 1)) × Fin (invLength i), y p ^ 2 :=
      Fintype.sum_equiv (indexEquiv k) _ _ fun i ↦ by
        simp [he, LinearEquiv.piCongrLeft]
    rw [h1, Fintype.sum_sigma]
  rw [hlhs, qCompare, QuadraticMap.comp_apply, pi_apply, mul_sum]
  refine sum_le_sum fun b _ ↦ ?_
  let z : (i : Fin (k + 1)) → Fin (invLength i) → ℤ :=
    (LinearEquiv.piCongrLeft ℤ (fun _ ↦ ℤ) (indexEquiv k) ≪≫ₗ
      LinearEquiv.piCurry ℤ fun _ (_ : Fin _) ↦ ℤ).toLinearMap (e.symm y)
  have hblock : ∀ j : Fin (invLength b),
      z b j = y ⟨b, j⟩ := by
    intro j
    simp [z, he, Sigma.curry]
  simp_rw [← hblock]
  induction b using Fin.cases with
  | zero =>
      change (∑ j : Fin 1, z 0 j ^ 2) ≤ 4 * HJO.q1 (z 0)
      exact sum_sq_le_four_mul_q1' _
  | succ b =>
      change (∑ j : Fin 3, z b.succ j ^ 2) ≤ 4 * HJO.q3011 (z b.succ)
      exact sum_sq_le_four_mul_q3011' _

/-- The sum-of-squares bound for `qModified` in the `b = 3k + 2` case. -/
theorem sum_sq_le_four_mul_qModified (k : ℕ) (n : (finspan {3, 3 * k + 2}).gaps → ℤ) :
    ∑ i, n i ^ 2 ≤ 4 * HJO.qModified (finspan {3, 3 * k + 2}).gaps 3 (3 * k + 2) n := by
  obtain ⟨y, rfl⟩ :=
    (LinearEquiv.piCongrLeft ℤ (fun _ : (finspan {3, 3 * k + 2}).gaps ↦ ℤ)
      (gapsEquiv k)).surjective n
  have key := DFunLike.congr_fun (qModified_comp_eq_qCompare k) y
  rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe] at key
  rw [key]
  refine le_of_eq_of_le ?_ (sum_sq_le_four_mul_qCompare k y)
  exact (Fintype.sum_equiv (gapsEquiv k) _ _ fun j ↦ by
    simp only [piCongrLeft_apply_const, Equiv.symm_apply_apply]).symm

end ThreeTwo

/-- `lem_quad_form_lower`. -/
theorem sum_sq_le_four_mul_Q (b : ℕ) {n : (finspan {3, b}).gaps → ℤ} (hn : 0 ≤ n) :
    ∑ i, n i ^ 2 ≤ 4 * HJO.Q 3 b n := by
  obtain h | h | h : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  · obtain ⟨k, rfl⟩ : ∃ k, b = 3 * k := ⟨b / 3, by omega⟩
    have hn0 : n = 0 := funext fun i ↦ absurd i.2 (by simp)
    subst hn0
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, b = 3 * k + 1 := ⟨b / 3, by omega⟩
    exact sum_sq_le_four_mul_Q'_of_qModified hn (ThreeOne.sum_sq_le_four_mul_qModified k n)
  · obtain ⟨k, rfl⟩ : ∃ k, b = 3 * k + 2 := ⟨b / 3, by omega⟩
    exact sum_sq_le_four_mul_Q'_of_qModified hn (ThreeTwo.sum_sq_le_four_mul_qModified k n)

/-- The bound on the cone, which is where the lattice sum's summand is supported. -/
theorem sum_sq_le_four_mul_Q_of_mem_cone (b : ℕ) {n : (finspan {3, b}).gaps → ℤ}
    (hn : n ∈ HJO.cone 3 b) : ∑ i, n i ^ 2 ≤ 4 * HJO.Q 3 b n :=
  sum_sq_le_four_mul_Q b (HJO.cone'_subset_Ici_zero _ _ _ hn)

end HJOA3.QuadForm
