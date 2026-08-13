module

public import QSeriesLib.NumberTheory.HJO.SumToSum.Defs

/-!
# Sum-to-sum conjecture for `b = 3k - 1`: definitions
-/

@[expose] public section

open Finset Polynomial NumericalSemigroup HJO HJO.SumToSum

namespace HJOA3.SumToSum.ThreeTwo

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

/-- The sum-to-sum conjecture for `(3, b)` with `b = 3k + 2`, i.e. -/
def Conjecture (k : ℕ) (r : Fin (k + 1) → ℕ) : Prop :=
  ∑ᶠ m, lhsTerm k r (finspan {3, 3 * k + 2}).gaps m = ∑ᶠ m, rhsTerm k r m

end HJOA3.SumToSum.ThreeTwo
