module

public import HJOA3.AndrewsGordon.Eight
public import HJOA3.AndrewsGordon.Five
public import HJOA3.AndrewsGordon.Four
public import HJOA3.AndrewsGordon.FourProduct
public import HJOA3.AndrewsGordon.Seven
public import HJOA3.EightFromKern
public import HJOA3.SumToSum.ThreeOne.QOne
public import HJOA3.SumToSum.ThreeOne.Seven
public import HJOA3.SumToSum.ThreeOne.Small
public import HJOA3.SumToSum.ThreeTwo.AtOne
public import HJOA3.SumToSum.ThreeTwo.Small
public import HJOA3.Tactic.Tag
public import HJOA3.WarnaarFive
public import HJOA3.WarnaarSeven

/-! # Satisfying the formal challenge -/

@[expose] public section

open Polynomial NumericalSemigroup HJO SumToSum

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

namespace HJOA3.Challenge

/-- **`thm_sum` — the sum-to-sum theorem.** The sum-to-sum conjecture holds at `b = 4, 5, 7, 8`. -/
theorem thm_sum :
    (∀ r₁ : ℕ, SumToSum.ThreeOne.Conjecture 1 ![r₁]) ∧
    (∀ r₁ r₂ : ℕ, r₂ ≤ r₁ → SumToSum.ThreeTwo.Conjecture 1 ![r₁, r₂]) ∧
    (∀ r₁ r₂ : ℕ, r₂ ≤ r₁ → SumToSum.ThreeOne.Conjecture 2 ![r₁, r₂]) ∧
    (∀ r₁ r₂ r₃ : ℕ, r₂ ≤ r₁ → r₃ ≤ r₂ → SumToSum.ThreeTwo.Conjecture 2 ![r₁, r₂, r₃]) :=
  ⟨SumToSum.ThreeOne.four,
   fun _ _ h ↦ SumToSum.ThreeTwo.five h,
   fun _ _ h ↦ SumToSum.ThreeOne.seven h,
   fun _ _ _ h₁ h₂ ↦ sumToSumEight h₁ h₂⟩

/-- **`thm_q1` — the `q = 1` theorem.** The sum-to-sum conjecture holds at `q = 1`, for
every `b > 3` coprime to `3`. -/
theorem thm_q1 (k : ℕ) (r : Fin (k + 1) → ℕ) (hr : Antitone r) :
    (∑ᶠ m, SumToSum.ThreeOne.lhsTerm (k + 1) r (gaps(3, 3 * (k + 1) + 1)) m).eval 1 =
      (∑ᶠ m, SumToSum.ThreeOne.rhsTerm (k + 1) r m).eval 1 ∧
    (∑ᶠ m, SumToSum.ThreeTwo.lhsTerm k r (gaps(3, 3 * k + 2)) m).eval 1 =
      (∑ᶠ m, SumToSum.ThreeTwo.rhsTerm k r m).eval 1 :=
  ⟨three_one_at_one k r hr, SumToSum.ThreeTwo.three_two_at_one k r hr⟩

/-- **`thm_main` — the main theorem.** The Huang–Jiang–Oblomkov conjecture holds for
`a = 3` and `b = 4, 5, 7, 8`, given Warnaar's Theorem 1.1. -/
theorem thm_main (hW : AndrewsGordon.Theorem11) :
    Conjecture 3 4 ∧ Conjecture 3 5 ∧ Conjecture 3 7 ∧ Conjecture 3 8 :=
  ⟨AndrewsGordon.conjecture_three_four_of_warnaar AndrewsGordon.thetaFour (hW.2 0),
   AndrewsGordon.conjecture_three_five_of_warnaar (hW.1 1),
   AndrewsGordon.conjecture_three_seven_of_warnaar (hW.2 1),
   AndrewsGordon.conjecture_three_eight_of_warnaar (hW.1 2)⟩

end HJOA3.Challenge
