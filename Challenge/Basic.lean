module

public import QSeriesLib.NumberTheory.HJO.Defs
public import QSeriesLib.NumberTheory.HJO.SumToSum.Defs
public import QSeriesLib.NumberTheory.QTheory.Basic

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

@[expose] public section

open Finset HJO

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

namespace HJOA3.SumToSum.ThreeTwo

open Polynomial NumericalSemigroup HJO.SumToSum

/-- The inner term in the summand of the LHS of `Conjecture`. -/
noncomputable def lhsTermInner
    (k : ℕ) (r : Fin (k + 1) → ℕ) (G : Finset ℕ) (n : G → ℕ) : ℕ[X] :=
  X ^ (Q' G 3 (3 * k + 2) (n ·)).toNat *
  (∏ j ∈ range k, qChoose X (extendNat n (3 * j + 4)) (extendNat n (3 * j + 1))) *
  (∏ j : Fin k, extendedQChoose X
    (r (Fin.castSucc j.rev) - extendNat n (3 * (j : ℕ) - 1))
    (extendNat n (3 * (j : ℕ) + 2) - extendNat n (3 * (j : ℕ) - 1)))

/-- The summand of the LHS of `Conjecture`. -/
noncomputable def lhsTerm
    (k : ℕ) (r : Fin (k + 1) → ℕ) (G : Finset ℕ) (n : G → ℕ) : ℕ[X] :=
  if ∀ j : Fin (k + 1), extendNat (n ·) (6 * k + 1 - 3 * (j : ℕ)) = r j then
    lhsTermInner k r G n
  else 0

/-- The summand of the RHS of `Conjecture`. -/
noncomputable def rhsTerm (k : ℕ) (r : Fin (k + 1) → ℕ) (m : Fin k → ℕ) : ℕ[X] :=
  X ^ (r (Fin.last k) ^ 2 +
    ∑ i : Fin k, (r i.castSucc ^ 2 + m i ^ 2 - r i.castSucc * m i)) *
  ∏ i : Fin k, if h : i.val + 1 = k then
    qChoose X (r i.castSucc + r (Fin.last k)) (m i)
  else
    qChoose X (r i.castSucc - r i.succ + m ⟨i + 1, lt_of_le_of_ne i.isLt h⟩) (m i)

/-- The sum-to-sum conjecture for `(3, b)` with `b = 3k + 2`. -/
def Conjecture (k : ℕ) (r : Fin (k + 1) → ℕ) : Prop :=
  ∑ᶠ m, lhsTerm k r (finspan {3, 3 * k + 2}).gaps m = ∑ᶠ m, rhsTerm k r m

end HJOA3.SumToSum.ThreeTwo

namespace HJOA3.AndrewsGordon

/-! ## Warnaar's Theorem 1.1 as hypothesis

S. O. Warnaar, *The `A₂` Andrews–Gordon identities and cylindric partitions*,
arXiv:2111.07550, Trans. Amer. Math. Soc. Ser. B **10** (2023) 715–765,
doi 10.1090/btran/147, **Theorem 1.1**: two families of identities, of modulus `3𝐤 + 2`
and `3𝐤 + 1`. This is the one external input the project assumes. -/

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

def quadExp (n m : ℕ) : ℕ := n ^ 2 + m ^ 2 - n * m

noncomputable def qPochhammerSelfInv (n : ℕ) : ℤ⟦X⟧ := invOfUnit (X; X)_n 1

/-- Warnaar's `θ(x; q) = (x; q)_∞ (q/x; q)_∞` at `(q, x) := (q^M, q^j)`. -/
noncomputable def theta1 (M j : ℕ) : ℤ⟦X⟧ :=
  (X ^ j; X ^ M)_∞ * (X ^ (M - j); X ^ M)_∞

/-- Warnaar's `θ(x, y, z; q)`, the product of three one-argument theta functions. -/
noncomputable def theta3 (M j₁ j₂ j₃ : ℕ) : ℤ⟦X⟧ :=
  theta1 M j₁ * theta1 M j₂ * theta1 M j₃

/-- The right side shared by both identities: `(q^M; q^M)_∞² / (q)_∞²` times a theta triple. -/
noncomputable def rhs (M j₁ j₂ j₃ : ℕ) : ℤ⟦X⟧ :=
  (X ^ M; X ^ M)_∞ ^ 2 * invOfUnit (X; X)_∞ 1 ^ 2 * theta3 M j₁ j₂ j₃

/-- The summand of `(1.10)`'s left side at `𝐤 = k + 1`. His convention `m_𝐤 := 2 n_𝐤` is
applied by `Fin.snoc`, so the `i = 𝐤 - 1` factor reads
`[n_{𝐤-1} - n_𝐤 + 2n_𝐤; m_{𝐤-1}]` as intended. -/
noncomputable def minusTerm (k : ℕ) (n : Fin (k + 1) → ℕ) (m : Fin k → ℕ) : ℤ⟦X⟧ :=
  let m' : Fin (k + 1) → ℕ := Fin.snoc m (2 * n (Fin.last k))
  X ^ (n (Fin.last k) ^ 2) * qPochhammerSelfInv (n 0) *
    ∏ i : Fin k,
      X ^ quadExp (n i.castSucc) (m' i.castSucc) *
        qChoose X (n i.castSucc) (n i.succ) *
        qChoose X (n i.castSucc - n i.succ + m' i.succ) (m' i.castSucc)

/-- The summand of `(1.11)`'s left side at `𝐤 = k + 2`. There is no `m_𝐤` convention here;
the family's distinguishing factor is the standalone `[2n_{𝐤-1}; m_{𝐤-1}]`. -/
noncomputable def plusTerm (k : ℕ) (n m : Fin (k + 1) → ℕ) : ℤ⟦X⟧ :=
  qPochhammerSelfInv (n 0) * qChoose X (2 * n (Fin.last k)) (m (Fin.last k)) *
    (∏ i : Fin (k + 1), X ^ quadExp (n i) (m i)) *
    ∏ i : Fin k,
      qChoose X (n i.castSucc) (n i.succ) *
        qChoose X (n i.castSucc - n i.succ + m i.succ) (m i.castSucc)

/-- The left side of `(1.10)` at `𝐤 = k + 1`. -/
noncomputable def minusLHS (k : ℕ) : ℤ⟦X⟧ :=
  ∑' p : (Fin (k + 1) → ℕ) × (Fin k → ℕ), minusTerm k p.1 p.2

/-- The right side of `(1.10)` at `𝐤 = k + 1`. -/
noncomputable def minusRHS (k : ℕ) : ℤ⟦X⟧ := rhs (3 * k + 5) (k + 1) (k + 2) (k + 2)

/-- **Warnaar `(1.10)` at `𝐤 = k + 1`**, modulus `3𝐤 + 2 = 3k + 5`. -/
def Minus (k : ℕ) : Prop := minusLHS k = minusRHS k

/-- The left side of `(1.11)` at `𝐤 = k + 2`. -/
noncomputable def plusLHS (k : ℕ) : ℤ⟦X⟧ :=
  ∑' p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ), plusTerm k p.1 p.2

/-- The right side of `(1.11)` at `𝐤 = k + 2`. -/
noncomputable def plusRHS (k : ℕ) : ℤ⟦X⟧ := rhs (3 * k + 7) (k + 2) (k + 2) (k + 3)

/-- **Warnaar `(1.11)` at `𝐤 = k + 2`**, modulus `3𝐤 + 1 = 3k + 7`. -/
def Plus (k : ℕ) : Prop := plusLHS k = plusRHS k

/-- **Warnaar's Theorem 1.1**, both families at every level: the sole external input
`thm_main` assumes. Only four instances are used — `Plus 0, 1` and
`Minus 1, 2` — but it is assumed whole, because that is the form the paper states
and therefore the form a reader can check. -/
def Theorem11 : Prop := (∀ k, Minus k) ∧ (∀ k, Plus k)

end HJOA3.AndrewsGordon

namespace HJOA3.Challenge

open Polynomial

/-- **`thm_sum` — the sum-to-sum theorem.** The sum-to-sum conjecture holds at `b = 4, 5, 7, 8`. -/
theorem thm_sum :
    (∀ r₁ : ℕ, SumToSum.ThreeOne.Conjecture 1 ![r₁]) ∧
    (∀ r₁ r₂ : ℕ, r₂ ≤ r₁ → SumToSum.ThreeTwo.Conjecture 1 ![r₁, r₂]) ∧
    (∀ r₁ r₂ : ℕ, r₂ ≤ r₁ → SumToSum.ThreeOne.Conjecture 2 ![r₁, r₂]) ∧
    (∀ r₁ r₂ r₃ : ℕ, r₂ ≤ r₁ → r₃ ≤ r₂ → SumToSum.ThreeTwo.Conjecture 2 ![r₁, r₂, r₃]) :=
  sorry

/-- **`thm_q1` — the `q = 1` theorem.** The sum-to-sum conjecture holds at `q = 1`, for
every `b > 3` coprime to `3`. -/
theorem thm_q1 (k : ℕ) (r : Fin (k + 1) → ℕ) (hr : Antitone r) :
    (∑ᶠ m, SumToSum.ThreeOne.lhsTerm (k + 1) r (gaps(3, 3 * (k + 1) + 1)) m).eval 1 =
      (∑ᶠ m, SumToSum.ThreeOne.rhsTerm (k + 1) r m).eval 1 ∧
    (∑ᶠ m, SumToSum.ThreeTwo.lhsTerm k r (gaps(3, 3 * k + 2)) m).eval 1 =
      (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm k r m).eval 1 :=
  sorry

/-- **`thm_main` — the main theorem.** The Huang–Jiang–Oblomkov conjecture holds for
`a = 3` and `b = 4, 5, 7, 8`, given Warnaar's Theorem 1.1. -/
theorem thm_main (hW : AndrewsGordon.Theorem11) :
    Conjecture 3 4 ∧ Conjecture 3 5 ∧ Conjecture 3 7 ∧ Conjecture 3 8 :=
  sorry

end HJOA3.Challenge
