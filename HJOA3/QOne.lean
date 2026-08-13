module

public import QSeriesLib.NumberTheory.HJO.SumToSum.Defs
public import QSeriesLib.NumberTheory.QTheory.Basic

/-!
# The `q = 1` specialization
-/

@[expose] public section

open Polynomial

namespace HJOA3

/-- At `q = 1` the `q`-binomial coefficient degenerates to the ordinary binomial coefficient. -/
@[simp] theorem qChoose_one_left {R : Type*} [CommSemiring R] :
    ∀ (n k : ℕ), qChoose (1 : R) n k = n.choose k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
      rw [qChoose_succ_succ, one_pow, one_mul, qChoose_one_left n k, qChoose_one_left n (k + 1),
        Nat.choose_succ_succ]
      push_cast
      ring

/-- Evaluating the polynomial `q`-binomial coefficient at `1`. -/
@[simp] theorem eval_one_qChoose :
    ∀ (n k : ℕ), (qChoose (X : ℕ[X]) n k).eval 1 = n.choose k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
      rw [qChoose_succ_succ, eval_add, eval_mul, eval_pow, eval_X, one_pow, one_mul,
        eval_one_qChoose n k, eval_one_qChoose n (k + 1), Nat.choose_succ_succ]

/--
The value of `HJO.SumToSum.extendedQChoose` at `q = 1`: the ordinary binomial coefficient,
still vanishing when either argument is negative.
-/
def extChoose (n r : ℤ) : ℕ := if 0 ≤ n ∧ 0 ≤ r then n.toNat.choose r.toNat else 0

@[simp] theorem extChoose_of_nonneg {n r : ℤ} (hn : 0 ≤ n) (hr : 0 ≤ r) :
    extChoose n r = n.toNat.choose r.toNat := if_pos ⟨hn, hr⟩

@[simp] theorem extChoose_of_neg {n r : ℤ} (h : n < 0 ∨ r < 0) : extChoose n r = 0 :=
  if_neg (by grind)

theorem extChoose_natCast (n r : ℕ) : extChoose (n : ℤ) (r : ℤ) = n.choose r := by
  rw [extChoose_of_nonneg (by positivity) (by positivity), Int.toNat_natCast, Int.toNat_natCast]

/--
At `q = 1`, the integer-argument `q`-binomial coefficient of `HJO.SumToSum` degenerates to the
ordinary binomial coefficient, still vanishing on negative arguments.
-/
theorem extendedQChoose_one_left {R : Type*} [CommSemiring R] (n r : ℤ) :
    HJO.SumToSum.extendedQChoose (1 : R) n r =
      if 0 ≤ n ∧ 0 ≤ r then (n.toNat.choose r.toNat : R) else 0 := by
  rw [HJO.SumToSum.extendedQChoose]
  split <;> simp

/-- Evaluating the integer-argument polynomial `q`-binomial coefficient at `1`. -/
@[simp] theorem eval_one_extendedQChoose (n r : ℤ) :
    (HJO.SumToSum.extendedQChoose (X : ℕ[X]) n r).eval 1 = extChoose n r := by
  rw [HJO.SumToSum.extendedQChoose, extChoose]
  split <;> simp

/-- `extChoose` vanishes when the numerator is smaller, after a common shift. -/
theorem extChoose_eq_zero_of_lt {a b p : ℤ} (h : a < b) : extChoose (a - p) (b - p) = 0 := by
  rcases lt_or_ge (a - p) 0 with h1 | h1
  · exact extChoose_of_neg (Or.inl h1)
  rcases lt_or_ge (b - p) 0 with h2 | h2
  · exact extChoose_of_neg (Or.inr h2)
  rw [extChoose_of_nonneg h1 h2, Nat.choose_eq_zero_of_lt]
  omega

/--
`eval 1` of a factor of `HJO.SumToSum.ThreeOne.rhsTerm`, with the `choose` kept *outside* the
conditional.
-/
theorem eval_one_rhsTerm_factor {k : ℕ} (r m : Fin k → ℕ) (i : Fin k) :
    (if h : i.val + 1 = k then qChoose (X : ℕ[X]) (2 * r i) (m i)
      else qChoose X (r i - r ⟨i.val + 1, by omega⟩ + m ⟨i.val + 1, by omega⟩) (m i)).eval 1 =
    (if h : i.val + 1 = k then 2 * r i
      else r i - r ⟨i.val + 1, by omega⟩ + m ⟨i.val + 1, by omega⟩).choose (m i) := by
  split_ifs <;> simp

end HJOA3
