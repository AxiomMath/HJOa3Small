module

public import QSeriesLib.Data.Fin.Tuple.Basic
public import QSeriesLib.Data.Fin.Tuple.Finset
public import QSeriesLib.NumberTheory.HJO.SumToSum.Small
public import QSeriesLib.NumberTheory.QTheory.Basic
public import QSeriesLib.NumberTheory.QTheory.Vandermonde
public import HJOA3.SumToSum.Grouping
import QSeriesLib.Tactic.Attr.Register
public meta import QSeriesLib.Tactic.ReduceNatFin -- shake: keep
import QSeriesLib.Tactic.ReduceNatFin

/-!
# Sum-to-sum identities for `b = 7`
-/

@[expose] public section

open Fin Finset Fintype Polynomial

namespace HJOA3.SumToSum.ThreeOne

/--
The integer-argument `q`-binomial coefficient of `HJO.SumToSum` agrees with the ordinary one
when both arguments are genuinely nonnegative.
-/
theorem extendedQChoose_sub (r n m : ℕ) (h₁ : n ≤ r) (h₂ : n ≤ m) :
    HJO.SumToSum.extendedQChoose (X : ℕ[X]) ((r : ℤ) - n) ((m : ℤ) - n) =
      qChoose X (r - n) (m - n) := by
  rw [HJO.SumToSum.extendedQChoose_of_nonneg (by omega) (by omega), Int.toNat_sub,
    Int.toNat_sub]

/-- The absorption identity in `ℕ[X]`. -/
theorem qChoose_mul_natPoly {n k s : ℕ} (hsk : s ≤ k) :
    qChoose (X : ℕ[X]) n k * qChoose X k s = qChoose X n s * qChoose X (n - s) (k - s) := by
  have hinj : Function.Injective (Polynomial.mapRingHom (Nat.castRingHom ℤ)) := by
    simpa [Polynomial.coe_mapRingHom] using
      Polynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective
  refine hinj ?_
  have hX : (Polynomial.mapRingHom (Nat.castRingHom ℤ)) (X : ℕ[X]) = X := by simp
  simp only [map_mul, map_qChoose, hX]
  exact qChoose_mul X hsk

/--
Splitting `qbinom{r₁ - n₁}{n₄ - n₁}` along `r₁ - n₁ = (r₁ - r₂) + (r₂ - n₁)` and absorbing
against `qbinom{r₂}{n₁}` replaces the pair by a sum over `c + (a - n₁) = n₄ - n₁`, with `a = n₁
+ p.2` playing the paper's role.
-/
theorem seven_step_one (r₁ r₂ n₁ n₄ : ℕ) (hn : n₁ ≤ r₂) (hr : r₂ ≤ r₁) :
    qChoose (X : ℕ[X]) r₂ n₁ * qChoose X (r₁ - n₁) (n₄ - n₁) =
    ∑ p ∈ (@Finset.HasAntidiagonal.antidiagonal ℕ _
      Finset.Nat.instHasAntidiagonal) (n₄ - n₁),
      X ^ ((r₁ - r₂ - p.1) * p.2) * qChoose X (r₁ - r₂) p.1 *
        (qChoose X r₂ (n₁ + p.2) * qChoose X (n₁ + p.2) n₁) := by
  rw [show r₁ - n₁ = (r₁ - r₂) + (r₂ - n₁) from by omega, qChoose_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have habs := qChoose_mul_natPoly (n := r₂) (k := n₁ + p.2) (s := n₁) (by omega)
  rw [Nat.add_sub_cancel_left] at habs
  rw [habs]
  ring

theorem seven_exponent_one (r₁ r₂ n₁ n₂ n₅ a c : ℤ) :
    n₁ ^ 2 + n₂ ^ 2 + (a + c) ^ 2 + n₅ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
        n₁ * n₂ - n₁ * r₂ + n₂ * (a + c) + (a + c) * n₅ - (a + c) * r₁ - n₂ * r₁ +
      (r₁ - r₂ - c) * (a - n₁) =
    (a - n₁) * n₂ + (a - n₁) * c + (n₅ - n₂) * c +
      (r₁ ^ 2 - r₁ * (n₁ + n₂ + c) + (n₁ + n₂ + c) ^ 2 +
        (a ^ 2 + a * n₅ + n₅ ^ 2 - a * r₂ + r₂ ^ 2)) := by
  ring

theorem seven_exponent_two (r₁ r₂ m₁ a n₅ : ℤ) :
    r₁ ^ 2 - r₁ * m₁ + m₁ ^ 2 + (a ^ 2 + a * n₅ + n₅ ^ 2 - a * r₂ + r₂ ^ 2) =
    (r₂ - a) * n₅ +
      (r₁ ^ 2 - r₁ * m₁ + m₁ ^ 2 + (r₂ ^ 2 - r₂ * (a + n₅) + (a + n₅) ^ 2)) := by
  ring

/-- The `b = 7` exponent is nonnegative on the relevant range. -/
theorem seven_exponent_nonneg (r₁ r₂ n₁ n₂ n₅ a c : ℕ)
    (h₁ : n₁ ≤ a) (ha : a ≤ r₂) (h₂ : n₂ ≤ n₅) (h₅ : n₅ ≤ r₂) (hr : r₂ ≤ r₁) :
    (0 : ℤ) ≤ (n₁ : ℤ) ^ 2 + n₂ ^ 2 + ((a : ℤ) + c) ^ 2 + n₅ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
      n₁ * n₂ - n₁ * r₂ + n₂ * ((a : ℤ) + c) + ((a : ℤ) + c) * n₅ -
        ((a : ℤ) + c) * r₁ - n₂ * r₁ := by
  have hn₁ : (0 : ℤ) ≤ (n₁ : ℤ) := by positivity
  have hn₂ : (0 : ℤ) ≤ (n₂ : ℤ) := by positivity
  have hc : (0 : ℤ) ≤ (c : ℤ) := by positivity
  have h₁' : (n₁ : ℤ) ≤ a := by exact_mod_cast h₁
  have ha' : (a : ℤ) ≤ r₂ := by exact_mod_cast ha
  have h₂' : (n₂ : ℤ) ≤ n₅ := by exact_mod_cast h₂
  have h₅' : (n₅ : ℤ) ≤ r₂ := by exact_mod_cast h₅
  have hr' : (r₂ : ℤ) ≤ r₁ := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r₁ : ℤ) - a - c), sq_nonneg ((r₂ : ℤ) - n₁),
    sq_nonneg ((r₁ : ℤ) - n₂), sq_nonneg ((a : ℤ) + c - n₅), sq_nonneg ((n₁ : ℤ) + n₂),
    sq_nonneg ((n₅ : ℤ) - n₂), mul_nonneg hn₁ hn₂, mul_nonneg hn₂ hc]

/-- `Q₂` is nonnegative. -/
theorem seven_exponent_two_nonneg (r₁ r₂ m₁ a n₅ : ℕ) :
    (0 : ℤ) ≤ (r₁ : ℤ) ^ 2 - r₁ * m₁ + (m₁ : ℤ) ^ 2 +
      ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2) := by
  have hn₅ : (0 : ℤ) ≤ (n₅ : ℤ) := by positivity
  have hr₂ : (0 : ℤ) ≤ (r₂ : ℤ) := by positivity
  nlinarith [sq_nonneg (2 * (r₁ : ℤ) - m₁), sq_nonneg (2 * (a : ℤ) + n₅ - r₂),
    sq_nonneg (m₁ : ℤ), mul_nonneg hn₅ hr₂]

/--
The `ℕ`-level form of `seven_exponent_one`, with the exponents as `Int.toNat` and the
differences as truncated subtraction.
-/
theorem seven_exponent_one_nat (r₁ r₂ n₁ n₂ n₅ a c : ℕ)
    (h₁ : n₁ ≤ a) (ha : a ≤ r₂) (h₂ : n₂ ≤ n₅) (h₅ : n₅ ≤ r₂) (hc : c ≤ r₁ - r₂)
    (hr : r₂ ≤ r₁) :
    ((n₁ : ℤ) ^ 2 + n₂ ^ 2 + ((a : ℤ) + c) ^ 2 + n₅ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
        n₁ * n₂ - n₁ * r₂ + n₂ * ((a : ℤ) + c) + ((a : ℤ) + c) * n₅ -
          ((a : ℤ) + c) * r₁ - n₂ * r₁).toNat + (r₁ - r₂ - c) * (a - n₁) =
    (a - n₁) * n₂ + (a - n₁) * c + (n₅ - n₂) * c +
      ((r₁ : ℤ) ^ 2 - r₁ * ((n₁ : ℤ) + n₂ + c) + ((n₁ : ℤ) + n₂ + c) ^ 2 +
        ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)).toNat := by
  have hE := seven_exponent_nonneg r₁ r₂ n₁ n₂ n₅ a c h₁ ha h₂ h₅ hr
  have hQ := seven_exponent_two_nonneg r₁ r₂ (n₁ + n₂ + c) a n₅
  push_cast at hQ
  have e1 : ((r₁ - r₂ - c : ℕ) : ℤ) = (r₁ : ℤ) - r₂ - c := by omega
  have e2 : ((a - n₁ : ℕ) : ℤ) = (a : ℤ) - n₁ := by omega
  have e3 : ((n₅ - n₂ : ℕ) : ℤ) = (n₅ : ℤ) - n₂ := by omega
  have key : (((n₁ : ℤ) ^ 2 + n₂ ^ 2 + ((a : ℤ) + c) ^ 2 + n₅ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
        n₁ * n₂ - n₁ * r₂ + n₂ * ((a : ℤ) + c) + ((a : ℤ) + c) * n₅ -
          ((a : ℤ) + c) * r₁ - n₂ * r₁).toNat : ℤ) + ((r₁ - r₂ - c : ℕ) * (a - n₁ : ℕ) : ℕ) =
      (((a - n₁ : ℕ) * n₂ + (a - n₁ : ℕ) * c + (n₅ - n₂ : ℕ) * c : ℕ) : ℤ) +
        (((r₁ : ℤ) ^ 2 - r₁ * ((n₁ : ℤ) + n₂ + c) + ((n₁ : ℤ) + n₂ + c) ^ 2 +
          ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hE, Int.toNat_of_nonneg hQ]
    push_cast [e1, e2, e3]
    ring
  exact_mod_cast key

/-- The change of variables `n₄ ↦ (a, c)` with `n₄ = a + c` and `a = n₁ + d`, as in §5.3. -/
theorem seven_reindex (r₁ r₂ n₁ : ℕ) (h₁ : n₁ ≤ r₂) (hr : r₂ ≤ r₁) (F : ℕ → ℕ[X]) :
    ∑ n₄ ∈ range (r₁ + 1),
        F n₄ * qChoose X r₂ n₁ *
          HJO.SumToSum.extendedQChoose X ((r₁ : ℤ) - n₁) ((n₄ : ℤ) - n₁) =
    ∑ a ∈ range (r₂ + 1), ∑ c ∈ range (r₁ - r₂ + 1),
      X ^ ((r₁ - r₂ - c) * (a - n₁)) * qChoose X (r₁ - r₂) c *
        (qChoose X r₂ a * qChoose X a n₁) * F (a + c) := by
  classical
  rw [← sum_range_shift_of_vanish h₁
      (fun a ↦ ∑ c ∈ range (r₁ - r₂ + 1),
        X ^ ((r₁ - r₂ - c) * (a - n₁)) * qChoose X (r₁ - r₂) c *
          (qChoose X r₂ a * qChoose X a n₁) * F (a + c))
      fun a ha ↦ Finset.sum_eq_zero fun c _ ↦ by
        rw [qChoose_eq_zero_of_lt ha]; ring]
  simp only [Nat.add_sub_cancel_left]
  have hsub : Finset.Ico n₁ (r₁ + 1) ⊆ range (r₁ + 1) := by
    intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  have hvan : ∀ n₄ ∈ range (r₁ + 1), n₄ ∉ Finset.Ico n₁ (r₁ + 1) →
      F n₄ * qChoose (X : ℕ[X]) r₂ n₁ *
        HJO.SumToSum.extendedQChoose X ((r₁ : ℤ) - n₁) ((n₄ : ℤ) - n₁) = 0 := by
    intro n₄ hn₄ hni
    simp only [Finset.mem_range] at hn₄
    simp only [Finset.mem_Ico, not_and, not_lt] at hni
    rw [HJO.SumToSum.extendedQChoose_of_neg_left (Or.inr (by omega))]
    ring
  rw [← Finset.sum_subset hsub hvan, Finset.sum_Ico_eq_sum_range,
    show r₁ + 1 - n₁ = r₁ - n₁ + 1 from by omega]
  have hterm : ∀ e ∈ range (r₁ - n₁ + 1),
      F (n₁ + e) * qChoose (X : ℕ[X]) r₂ n₁ *
          HJO.SumToSum.extendedQChoose X ((r₁ : ℤ) - n₁) (((n₁ + e : ℕ) : ℤ) - n₁) =
      ∑ p ∈ (@Finset.HasAntidiagonal.antidiagonal ℕ _
        Finset.Nat.instHasAntidiagonal) e,
        X ^ ((r₁ - r₂ - p.1) * p.2) * qChoose X (r₁ - r₂) p.1 *
          (qChoose X r₂ (n₁ + p.2) * qChoose X (n₁ + p.2) n₁) * F (n₁ + p.2 + p.1) := by
    intro e _
    rw [extendedQChoose_sub r₁ n₁ (n₁ + e) (by omega) (by omega),
      show F (n₁ + e) * qChoose (X : ℕ[X]) r₂ n₁ * qChoose X (r₁ - n₁) (n₁ + e - n₁) =
        qChoose (X : ℕ[X]) r₂ n₁ * qChoose X (r₁ - n₁) (n₁ + e - n₁) * F (n₁ + e) from by ring,
      seven_step_one r₁ r₂ n₁ (n₁ + e) h₁ hr, Nat.add_sub_cancel_left, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hp := (Finset.HasAntidiagonal.mem_antidiagonal
      (self := Finset.Nat.instHasAntidiagonal)).mp hp
    rw [show n₁ + e = n₁ + p.2 + p.1 from by omega]
  rw [Finset.sum_congr rfl hterm]
  refine (sum_box_eq_sum_antidiagonal (a := r₁ - r₂) (b := r₂ - n₁) (N := r₁ - n₁)
    (by omega)
    (f := fun c d ↦ X ^ ((r₁ - r₂ - c) * d) * qChoose X (r₁ - r₂) c *
      (qChoose X r₂ (n₁ + d) * qChoose X (n₁ + d) n₁) * F (n₁ + d + c))
    fun p hp ↦ ?_).symm
  rcases not_and_or.mp hp with h | h
  · rw [qChoose_eq_zero_of_lt (show r₁ - r₂ < p.1 from by omega)]
    ring
  · rw [qChoose_eq_zero_of_lt (show r₂ < n₁ + p.2 from by omega)]
    ring

theorem seven_term (r₁ r₂ n₁ n₂ n₅ a c : ℕ)
    (h₁ : n₁ ≤ a) (ha : a ≤ r₂) (h₂ : n₂ ≤ n₅) (h₅ : n₅ ≤ r₂) (hc : c ≤ r₁ - r₂)
    (hr : r₂ ≤ r₁) :
    (X : ℕ[X]) ^ ((r₁ - r₂ - c) * (a - n₁)) * qChoose X (r₁ - r₂) c *
        (qChoose X r₂ a * qChoose X a n₁) *
        (X ^ ((n₁ : ℤ) ^ 2 + n₂ ^ 2 + ((a + c : ℕ) : ℤ) ^ 2 + n₅ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
              n₁ * n₂ - n₁ * r₂ + n₂ * ((a + c : ℕ) : ℤ) + ((a + c : ℕ) : ℤ) * n₅ -
              ((a + c : ℕ) : ℤ) * r₁ - n₂ * r₁).toNat *
          qChoose X n₅ n₂ * qChoose X r₂ n₅) =
    X ^ ((a - n₁) * n₂ + (a - n₁) * c + (n₅ - n₂) * c) *
      (qChoose X a n₁ * qChoose X n₅ n₂ * qChoose X (r₁ - r₂) c) *
      (X ^ ((r₁ : ℤ) ^ 2 - r₁ * ((n₁ + n₂ + c : ℕ) : ℤ) + ((n₁ + n₂ + c : ℕ) : ℤ) ^ 2 +
            ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)).toNat *
        (qChoose X r₂ a * qChoose X r₂ n₅)) := by
  have hexp := seven_exponent_one_nat r₁ r₂ n₁ n₂ n₅ a c h₁ ha h₂ h₅ hc hr
  push_cast
  calc (X : ℕ[X]) ^ ((r₁ - r₂ - c) * (a - n₁)) * qChoose X (r₁ - r₂) c *
        (qChoose X r₂ a * qChoose X a n₁) *
        (X ^ ((n₁ : ℤ) ^ 2 + n₂ ^ 2 + ((a : ℤ) + c) ^ 2 + n₅ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
              n₁ * n₂ - n₁ * r₂ + n₂ * ((a : ℤ) + c) + ((a : ℤ) + c) * n₅ -
              ((a : ℤ) + c) * r₁ - n₂ * r₁).toNat *
          qChoose X n₅ n₂ * qChoose X r₂ n₅)
      = X ^ (((n₁ : ℤ) ^ 2 + n₂ ^ 2 + ((a : ℤ) + c) ^ 2 + n₅ ^ 2 + r₂ ^ 2 + r₁ ^ 2 +
              n₁ * n₂ - n₁ * r₂ + n₂ * ((a : ℤ) + c) + ((a : ℤ) + c) * n₅ -
              ((a : ℤ) + c) * r₁ - n₂ * r₁).toNat + (r₁ - r₂ - c) * (a - n₁)) *
          (qChoose X (r₁ - r₂) c * qChoose X r₂ a * qChoose X a n₁ * qChoose X n₅ n₂ *
            qChoose X r₂ n₅) := by
        rw [pow_add]; ring
    _ = X ^ ((a - n₁) * n₂ + (a - n₁) * c + (n₅ - n₂) * c +
            ((r₁ : ℤ) ^ 2 - r₁ * ((n₁ : ℤ) + n₂ + c) + ((n₁ : ℤ) + n₂ + c) ^ 2 +
              ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)).toNat) *
          (qChoose X (r₁ - r₂) c * qChoose X r₂ a * qChoose X a n₁ * qChoose X n₅ n₂ *
            qChoose X r₂ n₅) := by
        rw [hexp]
    _ = _ := by rw [pow_add]; ring

/--
The `ℕ`-level form of `seven_exponent_two`, landing directly in the truncated-subtraction shape
of `seven_iff`'s right-hand exponent.
-/
theorem seven_exponent_two_nat (r₁ r₂ m₁ a n₅ : ℕ) (ha : a ≤ r₂) :
    ((r₁ : ℤ) ^ 2 - r₁ * (m₁ : ℤ) + (m₁ : ℤ) ^ 2 +
      ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)).toNat =
    (r₂ - a) * n₅ +
      ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + (a + n₅) ^ 2 - r₂ * (a + n₅))) := by
  have b1 : r₁ * m₁ ≤ r₁ ^ 2 + m₁ ^ 2 := by
    rcases le_total r₁ m₁ with h | h
    · nlinarith
    · nlinarith
  have b2 : r₂ * (a + n₅) ≤ r₂ ^ 2 + (a + n₅) ^ 2 := by
    rcases le_total r₂ (a + n₅) with h | h
    · nlinarith
    · nlinarith
  have key : ((r₁ : ℤ) ^ 2 - r₁ * (m₁ : ℤ) + (m₁ : ℤ) ^ 2 +
      ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)) =
      (((r₂ - a) * n₅ +
        ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + (a + n₅) ^ 2 - r₂ * (a + n₅))) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub ha, Nat.cast_sub b1, Nat.cast_sub b2]
    ring
  rw [key, Int.toNat_natCast]

theorem seven_term' (r₁ r₂ m₁ a n₅ : ℕ) (ha : a ≤ r₂) :
    qChoose (X : ℕ[X]) (a + n₅ + (r₁ - r₂)) m₁ *
        (X ^ ((r₁ : ℤ) ^ 2 - r₁ * (m₁ : ℤ) + (m₁ : ℤ) ^ 2 +
            ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)).toNat *
          (qChoose X r₂ a * qChoose X r₂ n₅)) =
    X ^ ((r₂ - a) * n₅) * (qChoose X r₂ a * qChoose X r₂ n₅) *
      (X ^ ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + (a + n₅) ^ 2 - r₂ * (a + n₅))) *
        qChoose X (r₁ - r₂ + (a + n₅)) m₁) := by
  rw [seven_exponent_two_nat r₁ r₂ m₁ a n₅ ha, pow_add,
    show a + n₅ + (r₁ - r₂) = r₁ - r₂ + (a + n₅) from by omega]
  ring

theorem seven_step_two (r₁ r₂ a n₅ : ℕ) (g : ℕ → ℕ[X]) :
    ∑ n₁ ∈ range (a + 1), ∑ n₂ ∈ range (n₅ + 1), ∑ c ∈ range (r₁ - r₂ + 1),
      X ^ ((a - n₁) * n₂ + (a - n₁) * c + (n₅ - n₂) * c) *
        (qChoose X a n₁ * qChoose X n₅ n₂ * qChoose X (r₁ - r₂) c) * g (n₁ + n₂ + c) =
    ∑ m₁ ∈ range (a + n₅ + (r₁ - r₂) + 1),
      qChoose X (a + n₅ + (r₁ - r₂)) m₁ * g m₁ := by
  have h := sum_box_weighted (X : ℕ[X]) (n := ![a, n₅, r₁ - r₂]) g
  rw [sum_piFinset_fin_three] at h
  simpa [Fin.sum_univ_three, Fin.prod_univ_three, Finset.sum_filter, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    add_assoc, mul_assoc] using h

theorem seven_step_three (r₂ : ℕ) (g : ℕ → ℕ[X]) :
    ∑ a ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₂ + 1),
      X ^ ((r₂ - a) * n₅) * (qChoose X r₂ a * qChoose X r₂ n₅) * g (a + n₅) =
    ∑ m₂ ∈ range (2 * r₂ + 1), qChoose X (2 * r₂) m₂ * g m₂ := by
  have h := sum_box_weighted (X : ℕ[X]) (n := ![r₂, r₂]) g
  simpa [Fin.sum_univ_two, Fin.prod_univ_two, Finset.sum_filter, sum_piFinset_fin_succ,
    sum_piFinset_fin_zero, reduce_tail, Matrix.empty_eq elim0, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, two_mul, mul_assoc] using h

/-- The sum-to-sum conjecture holds for `b = 7`. -/
theorem seven {r₁ r₂ : ℕ} (hr : r₂ ≤ r₁) :
    HJO.SumToSum.ThreeOne.Conjecture 2 ![r₁, r₂] := by
  refine (HJO.SumToSum.ThreeOne.seven_iff r₁ r₂ hr).mpr ?_
  rw [Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_comm]
  rw [Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun n₁ hn₁ ↦ Finset.sum_congr rfl fun n₂ _ ↦
    Finset.sum_congr rfl fun n₅ _ ↦
      seven_reindex r₁ r₂ n₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₁)) hr _) ?_
  rw [Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_congr rfl fun n₂ _ ↦ Finset.sum_comm]
  rw [Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_comm]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun n₁ _ ↦ Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun n₅ _ ↦
    sum_range_shrink (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) _ ?_) ?_
  · intro n₁ hn₁
    refine Finset.sum_eq_zero fun n₂ _ ↦ Finset.sum_eq_zero fun c _ ↦ ?_
    rw [qChoose_eq_zero_of_lt hn₁]
    ring
  refine Eq.trans (Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun n₅ hn₅ ↦
    Finset.sum_congr rfl fun n₁ _ ↦
      sum_range_shrink (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₅)) _ ?_) ?_
  · intro n₂ hn₂
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    rw [qChoose_eq_zero_of_lt hn₂]
    ring
  refine Eq.trans (Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun n₅ hn₅ ↦
    Eq.trans (Finset.sum_congr rfl fun n₁ hn₁ ↦ Finset.sum_congr rfl fun n₂ hn₂ ↦
      Finset.sum_congr rfl fun c hc ↦
        seven_term r₁ r₂ n₁ n₂ n₅ a c
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₁))
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₂))
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₅))
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)) hr)
      (seven_step_two r₁ r₂ a n₅ (fun m₁ ↦
        X ^ ((r₁ : ℤ) ^ 2 - r₁ * (m₁ : ℤ) + (m₁ : ℤ) ^ 2 +
            ((a : ℤ) ^ 2 + a * n₅ + (n₅ : ℤ) ^ 2 - a * r₂ + (r₂ : ℤ) ^ 2)).toNat *
          (qChoose X r₂ a * qChoose X r₂ n₅)))) ?_
  refine Eq.trans (Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun n₅ hn₅ ↦
    (sum_range_shrink (show a + n₅ + (r₁ - r₂) ≤ 2 * r₁ from by
        have h1 : a ≤ r₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have h2 : n₅ ≤ r₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn₅)
        omega) _ ?_).symm) ?_
  · intro m₁ hm₁
    rw [qChoose_eq_zero_of_lt hm₁]
    ring
  rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun m₁ _ ↦
    Eq.trans (Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun n₅ _ ↦
      seven_term' r₁ r₂ m₁ a n₅ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
      (seven_step_three r₂ (fun m₂ ↦
        X ^ ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂)) *
          qChoose X (r₁ - r₂ + m₂) m₁))) ?_
  refine Eq.trans (Finset.sum_congr rfl fun m₁ _ ↦
    (sum_range_shrink (show 2 * r₂ ≤ 2 * r₁ from by omega) _ ?_).symm) ?_
  · intro m₂ hm₂
    rw [qChoose_eq_zero_of_lt hm₂]
    ring
  · exact Finset.sum_congr rfl fun m₁ _ ↦ Finset.sum_congr rfl fun m₂ _ ↦ by ring

end HJOA3.SumToSum.ThreeOne
