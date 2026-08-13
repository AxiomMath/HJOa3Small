module

public import QSeriesLib.NumberTheory.QTheory.Basic
public import QSeriesLib.NumberTheory.QTheory.Vandermonde
public import HJOA3.SumToSum.Box
public import HJOA3.SumToSum.ThreeTwo.EightRec
import Mathlib.Tactic.Ring

/-!
# `BaseEight` at the bottom level `r₁ = r₂`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3

/-- `q`-Vandermonde in range form. -/
theorem qChoose_add_range {R : Type*} [CommSemiring R] (q : R) (m n r : ℕ) :
    qChoose q (m + n) r =
      ∑ k ∈ range (r + 1), q ^ ((m - k) * (r - k)) * qChoose q m k * qChoose q n (r - k) := by
  rw [qChoose_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y ↦ q ^ ((m - x) * y) * qChoose q m x * qChoose q n y) r]

/-- `qChoose_mul` over a commutative semiring. -/
theorem qChoose_mul_semiring {R : Type*} [CommSemiring R] (q : R) {n k s : ℕ} (hsk : s ≤ k) :
    qChoose q n k * qChoose q k s = qChoose q n s * qChoose q (n - s) (k - s) := by
  have hnat : qChoose (X : ℕ[X]) n k * qChoose X k s
      = qChoose (X : ℕ[X]) n s * qChoose X (n - s) (k - s) := by
    refine Polynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective ?_
    have hmap : ∀ p : ℕ[X], Polynomial.map (Nat.castRingHom ℤ) p
        = Polynomial.mapRingHom (Nat.castRingHom ℤ) p := fun _ ↦ rfl
    have hX : Polynomial.mapRingHom (Nat.castRingHom ℤ) (X : ℕ[X]) = X := by
      rw [← hmap]; exact Polynomial.map_X _
    simp only [hmap, map_mul, map_qChoose, hX]
    exact qChoose_mul (X : ℤ[X]) hsk
  have hq : (Polynomial.eval₂RingHom (Nat.castRingHom R) q) (X : ℕ[X]) = q := by simp
  simpa only [map_mul, map_qChoose, hq] using
    congr_arg (Polynomial.eval₂RingHom (Nat.castRingHom R) q) hnat

/-- Regrouping a box by its coordinate sums. -/
theorem sum_box_eq_sum_range_range {M : Type*} [AddCommMonoid M] (A B N : ℕ) (hAB : A + B ≤ N)
    (g : ℕ → ℕ → M) (hg : ∀ c d, A < c ∨ B < d → g c d = 0) :
    (∑ c ∈ range (A + 1), ∑ d ∈ range (B + 1), g c d)
      = ∑ m ∈ range (N + 1), ∑ k ∈ range (m + 1), g k (m - k) := by
  have hzero : ∀ p : ℕ × ℕ, ¬(p.1 ≤ A ∧ p.2 ≤ B) → g p.1 p.2 = 0 :=
    fun p hp ↦ hg _ _ (by omega)
  calc (∑ c ∈ range (A + 1), ∑ d ∈ range (B + 1), g c d)
      = ∑ d ∈ range (B + 1), ∑ c ∈ range (A + 1), g c d := Finset.sum_comm
    _ = ∑ m ∈ range (N + 1), ∑ p ∈ (@Finset.HasAntidiagonal.antidiagonal ℕ _
        Finset.Nat.instHasAntidiagonal) m, g p.1 p.2 :=
        sum_box_eq_sum_antidiagonal hAB g hzero
    _ = _ := Finset.sum_congr rfl fun m _ ↦
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p ↦ g p.1 p.2) m

namespace SumToSum.ThreeTwo

/--
The exponent splits into a function of the two coordinate sums plus the two `q`-Vandermonde
cross terms.
-/
theorem eightExp_eq_natCast_split {r₁ r₂ r₃ n₁ n₂ n₄ n₅ : ℕ} (h₁₄ : n₁ ≤ n₄) (h₄ : n₄ ≤ r₃) :
    eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅ =
      ((r₃ ^ 2 + ((r₂ ^ 2 + (n₁ + n₂) ^ 2 - r₂ * (n₁ + n₂)) +
        (r₁ ^ 2 + (n₄ + n₅) ^ 2 - r₁ * (n₄ + n₅))) + (n₄ - n₁) * n₂ + (r₃ - n₄) * n₅ : ℕ) : ℤ) := by
  have hb₁ : r₂ * (n₁ + n₂) ≤ r₂ ^ 2 + (n₁ + n₂) ^ 2 := by
    nlinarith [sq_nonneg (r₂ - (n₁ + n₂)), sq_nonneg ((n₁ + n₂) - r₂)]
  have hb₂ : r₁ * (n₄ + n₅) ≤ r₁ ^ 2 + (n₄ + n₅) ^ 2 := by
    nlinarith [sq_nonneg (r₁ - (n₄ + n₅)), sq_nonneg ((n₄ + n₅) - r₁)]
  simp only [eightExp]
  push_cast [Nat.cast_sub hb₁, Nat.cast_sub hb₂, Nat.cast_sub h₁₄, Nat.cast_sub h₄]
  ring

/-- The split, on `.toNat`. -/
theorem eightExp_toNat_split {r₁ r₂ r₃ n₁ n₂ n₄ n₅ : ℕ} (h₁₄ : n₁ ≤ n₄) (h₄ : n₄ ≤ r₃) :
    (eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅).toNat =
      r₃ ^ 2 + ((r₂ ^ 2 + (n₁ + n₂) ^ 2 - r₂ * (n₁ + n₂)) +
          (r₁ ^ 2 + (n₄ + n₅) ^ 2 - r₁ * (n₄ + n₅))) + (n₄ - n₁) * n₂ + (r₃ - n₄) * n₅ := by
  rw [eightExp_eq_natCast_split h₁₄ h₄, Int.toNat_natCast]

/-- The two nested `q`-Vandermonde convolutions. -/
theorem sum_vandermonde_block {R : Type*} [CommSemiring R] (q : R) (r r₃ m₁ m₂ : ℕ) :
    (∑ n₄ ∈ range (m₂ + 1),
      q ^ ((r₃ - n₄) * (m₂ - n₄)) * qChoose q r₃ n₄ * qChoose q r (m₂ - n₄) *
        (∑ n₁ ∈ range (m₁ + 1),
          q ^ ((n₄ - n₁) * (m₁ - n₁)) * qChoose q n₄ n₁ * qChoose q (m₂ - n₄) (m₁ - n₁)))
      = qChoose q (r + r₃) m₂ * qChoose q m₂ m₁ := by
  have hinner : ∀ n₄ ∈ range (m₂ + 1),
      (∑ n₁ ∈ range (m₁ + 1),
        q ^ ((n₄ - n₁) * (m₁ - n₁)) * qChoose q n₄ n₁ * qChoose q (m₂ - n₄) (m₁ - n₁))
        = qChoose q m₂ m₁ := by
    intro n₄ hn₄
    simp only [mem_range, Nat.lt_succ_iff] at hn₄
    rw [(qChoose_add_range q n₄ (m₂ - n₄) m₁).symm, show n₄ + (m₂ - n₄) = m₂ from by omega]
  rw [Finset.sum_congr rfl fun n₄ hn₄ ↦ by rw [hinner n₄ hn₄], ← Finset.sum_mul, add_comm r r₃]
  exact congrArg (· * qChoose q m₂ m₁) (qChoose_add_range q r₃ r m₂).symm

/-- `eightRHS` at `r₁ = r₂`, with each summand expanded into the two convolutions. -/
theorem eightRHS_eq_sum_block (r r₃ : ℕ) :
    eightRHS r r r₃ =
      ∑ m₁ ∈ range (2 * r + 1), ∑ m₂ ∈ range (2 * r + 1),
        X ^ (r₃ ^ 2 + ((r ^ 2 + m₁ ^ 2 - r * m₁) + (r ^ 2 + m₂ ^ 2 - r * m₂))) *
          (∑ n₄ ∈ range (m₂ + 1),
            X ^ ((r₃ - n₄) * (m₂ - n₄)) * qChoose X r₃ n₄ * qChoose X r (m₂ - n₄) *
              (∑ n₁ ∈ range (m₁ + 1),
                X ^ ((n₄ - n₁) * (m₁ - n₁)) * qChoose X n₄ n₁ *
                  qChoose X (m₂ - n₄) (m₁ - n₁))) := by
  rw [eightRHS]
  refine Finset.sum_congr rfl fun m₁ _ ↦ Finset.sum_congr rfl fun m₂ _ ↦ ?_
  rw [sum_vandermonde_block (X : ℕ[X]) r r₃ m₁ m₂, show r - r + m₂ = m₂ from by omega]
  ring

/-- The regrouping, over an arbitrary semiring. -/
theorem sum_box_eq_sum_block {M : Type*} [CommSemiring M] (X : M) (C : ℕ → ℕ → M)
    (hCzero : ∀ n k, n < k → C n k = 0) (A B N : ℕ) (base : ℕ → ℕ → ℕ) (hAB : A + B ≤ N) :
    (∑ n₂ ∈ range (B + 1), ∑ n₅ ∈ range (B + 1),
      ∑ n₁ ∈ range (A + 1), ∑ n₄ ∈ range (A + 1),
        X ^ base (n₁ + n₂) (n₄ + n₅) *
          X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
          C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂ : M)
      = ∑ m₁ ∈ range (N + 1), ∑ m₂ ∈ range (N + 1),
          X ^ base m₁ m₂ *
            (∑ n₄ ∈ range (m₂ + 1),
              X ^ ((A - n₄) * (m₂ - n₄)) * C A n₄ * C B (m₂ - n₄) *
                (∑ n₁ ∈ range (m₁ + 1),
                  X ^ ((n₄ - n₁) * (m₁ - n₁)) * C n₄ n₁ * C (m₂ - n₄) (m₁ - n₁))) := by
  rw [Finset.sum_congr rfl (fun n₂ _ ↦ Finset.sum_congr rfl (fun n₅ _ ↦
      Finset.sum_comm (f := fun n₁ n₄ ↦
        X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
          C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂)))]
  rw [Finset.sum_congr rfl (fun n₂ _ ↦ Finset.sum_comm
      (f := fun n₅ n₄ ↦ ∑ n₁ ∈ range (A + 1),
        X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
          C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂))]
  rw [Finset.sum_comm (f := fun n₂ n₄ ↦ ∑ n₅ ∈ range (B + 1), ∑ n₁ ∈ range (A + 1),
        X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
          C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂)]
  rw [Finset.sum_congr rfl (fun n₄ _ ↦
    (by
      rw [Finset.sum_comm (f := fun n₂ n₅ ↦ ∑ n₁ ∈ range (A + 1),
        X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
          C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂)]
      rw [Finset.sum_congr rfl (fun n₅ _ ↦
        Finset.sum_comm (f := fun n₂ n₁ ↦
          X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
            C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂))]
      : (∑ n₂ ∈ range (B + 1), ∑ n₅ ∈ range (B + 1), ∑ n₁ ∈ range (A + 1),
          X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
            C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂)
        = ∑ n₅ ∈ range (B + 1), ∑ n₁ ∈ range (A + 1), ∑ n₂ ∈ range (B + 1),
          X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
            C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂))]
  set g' : ℕ → ℕ → M := fun n₄ n₅ ↦
    ∑ n₁ ∈ range (A + 1), ∑ n₂ ∈ range (B + 1),
      X ^ (base (n₁ + n₂) (n₄ + n₅)) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * n₅) *
        C n₄ n₁ * C A n₄ * C B n₅ * C n₅ n₂ with hg'def
  have hg' : ∀ c d, A < c ∨ B < d → g' c d = 0 := by
    intro c d hcd
    simp only [hg'def]
    refine Finset.sum_eq_zero fun n₁ _ ↦ Finset.sum_eq_zero fun n₂ _ ↦ ?_
    rcases hcd with hc | hd
    · rw [hCzero _ _ hc]; ring
    · rw [hCzero _ _ hd]; ring
  rw [sum_box_eq_sum_range_range A B N hAB g' hg']
  rw [Finset.sum_comm (s := range (N + 1)) (t := range (N + 1))
    (f := fun m₁ m₂ ↦
      X ^ base m₁ m₂ *
        ∑ n₄ ∈ range (m₂ + 1),
          X ^ ((A - n₄) * (m₂ - n₄)) * C A n₄ * C B (m₂ - n₄) *
            ∑ n₁ ∈ range (m₁ + 1), X ^ ((n₄ - n₁) * (m₁ - n₁)) * C n₄ n₁ * C (m₂ - n₄) (m₁ - n₁))]
  refine Finset.sum_congr rfl fun m₂ hm₂ ↦ ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hm₂
  rw [Finset.sum_congr rfl (fun m₁ _ ↦ Finset.mul_sum (range (m₂ + 1)) _ _)]
  rw [Finset.sum_comm (s := range (N + 1)) (t := range (m₂ + 1))
    (f := fun m₁ n₄ ↦
      X ^ base m₁ m₂ *
        (X ^ ((A - n₄) * (m₂ - n₄)) * C A n₄ * C B (m₂ - n₄) *
          ∑ n₁ ∈ range (m₁ + 1), X ^ ((n₄ - n₁) * (m₁ - n₁)) * C n₄ n₁ * C (m₂ - n₄) (m₁ - n₁)))]
  refine Finset.sum_congr rfl fun n₄ hn₄ ↦ ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hn₄
  simp only [hg'def]
  rw [show n₄ + (m₂ - n₄) = m₂ from by omega]
  by_cases hle : m₂ - n₄ ≤ B
  · set g'' : ℕ → ℕ → M := fun n₁ n₂ ↦
      X ^ (base (n₁ + n₂) m₂) * X ^ ((n₄ - n₁) * n₂) * X ^ ((A - n₄) * (m₂ - n₄)) *
        C n₄ n₁ * C A n₄ * C B (m₂ - n₄) * C (m₂ - n₄) n₂ with hg''def
    have hg'' : ∀ c d, A < c ∨ B < d → g'' c d = 0 := by
      intro c d hcd
      simp only [hg''def]
      rcases hcd with hc | hd
      · by_cases hn₄A : n₄ ≤ A
        · rw [hCzero _ _ (show n₄ < c from by omega)]; ring
        · rw [hCzero _ _ (show A < n₄ from by omega)]; ring
      · rw [hCzero _ _ (show m₂ - n₄ < d from by omega)]; ring
    change (∑ n₁ ∈ range (A + 1), ∑ n₂ ∈ range (B + 1), g'' n₁ n₂) = _
    rw [sum_box_eq_sum_range_range A B N hAB g'' hg'']
    refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n₁ hn₁ ↦ ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hn₁
    simp only [hg''def]
    rw [show n₁ + (m₁ - n₁) = m₁ from by omega]
    ring
  · have hz : C B (m₂ - n₄) = 0 := hCzero _ _ (by omega)
    trans (0 : M)
    · exact Finset.sum_eq_zero fun n₁ _ ↦ Finset.sum_eq_zero fun n₂ _ ↦ by rw [hz]; ring
    · exact (Finset.sum_eq_zero fun m₁ _ ↦ by rw [hz]; ring).symm

/-- `BaseEight`'s first conjunct: the `b = 8` identity at `r₁ = r₂`. -/
theorem eightLHS_eq_eightRHS_self (r r₃ : ℕ) (h₃ : r₃ ≤ r) :
    eightLHS r r r₃ = eightRHS r r r₃ := by
  rw [eightLHS_eq_guarded r r r₃ le_rfl, eightRHS_eq_sum_block]
  have hprep : (∑ n₂ ∈ range (r + 1), ∑ n₅ ∈ range (r + 1),
      ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
        X ^ (eightExp r r r₃ n₁ n₂ n₄ n₅).toNat *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r n₂ *
          (if n₂ ≤ n₅ then qChoose X (r - n₂) (n₅ - n₂) else 0) : ℕ[X])
      = ∑ n₂ ∈ range (r + 1), ∑ n₅ ∈ range (r + 1),
          ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
            X ^ (r₃ ^ 2 + ((r ^ 2 + (n₁ + n₂) ^ 2 - r * (n₁ + n₂)) +
                (r ^ 2 + (n₄ + n₅) ^ 2 - r * (n₄ + n₅)))) *
              X ^ ((n₄ - n₁) * n₂) * X ^ ((r₃ - n₄) * n₅) *
              qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r n₅ * qChoose X n₅ n₂ := by
    refine Finset.sum_congr rfl fun n₂ hn₂ ↦ Finset.sum_congr rfl fun n₅ hn₅ ↦
      Finset.sum_congr rfl fun n₁ hn₁ ↦ Finset.sum_congr rfl fun n₄ hn₄ ↦ ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hn₂ hn₅ hn₁ hn₄
    by_cases hn₁₄ : n₁ ≤ n₄
    · by_cases hn₂₅ : n₂ ≤ n₅
      · rw [if_pos hn₂₅]
        rw [eightExp_toNat_split hn₁₄ hn₄, pow_add, pow_add,
          mul_assoc _ (qChoose (X : ℕ[X]) r n₂) (qChoose X (r - n₂) (n₅ - n₂)),
          show qChoose (X : ℕ[X]) r n₂ * qChoose X (r - n₂) (n₅ - n₂)
            = qChoose X r n₅ * qChoose X n₅ n₂ from (qChoose_mul_semiring X hn₂₅).symm]
        ring
      · rw [if_neg hn₂₅, qChoose_eq_zero_of_lt (show n₅ < n₂ from by omega)]
        ring
    · rw [qChoose_eq_zero_of_lt (show n₄ < n₁ from by omega)]
      ring
  rw [hprep]
  exact sum_box_eq_sum_block (X : ℕ[X]) (fun n k ↦ qChoose X n k)
    (fun _ _ h ↦ qChoose_eq_zero_of_lt h) r₃ r (2 * r)
    (fun m₁ m₂ ↦ r₃ ^ 2 + ((r ^ 2 + m₁ ^ 2 - r * m₁) + (r ^ 2 + m₂ ^ 2 - r * m₂)))
    (by omega)

/-- `BaseEight` is now the level `r₁ = r₂ + 1` statement alone. -/
theorem baseEight_of_succ
    (h : ∀ r₂ r₃ : ℕ, r₃ ≤ r₂ → eightLHS (r₂ + 1) r₂ r₃ = eightRHS (r₂ + 1) r₂ r₃) :
    BaseEight :=
  fun r₂ r₃ h₃ ↦ ⟨eightLHS_eq_eightRHS_self r₂ r₃ h₃, h r₂ r₃ h₃⟩

end SumToSum.ThreeTwo

end HJOA3
