module

public meta import HJOA3.SumToSum.ThreeTwo.AtOne
public meta import HJOA3.SumToSum.ThreeTwo.QOne

/-!
# Index tests for `HJOA3.SumToSum.ThreeTwo.Defs`
-/

set_option linter.hashCommand false

open Finset NumericalSemigroup

namespace HJOA3.SumToSum.ThreeTwo

example : (finspan {3, 3 * 1 + 2}).gaps = {1, 2, 4, 7} := rfl
example : (finspan {3, 3 * 2 + 2}).gaps = {1, 2, 4, 5, 7, 10, 13} := rfl

example : (List.finRange 2).map (fun j : Fin 2 ↦ 6 * 1 + 1 - 3 * (j : ℕ)) = [7, 4] := rfl
example : (List.finRange 3).map (fun j : Fin 3 ↦ 6 * 2 + 1 - 3 * (j : ℕ)) = [13, 10, 7] := rfl

example : (List.range 2).map (fun j ↦ 3 * j + 4) = [4, 7] := rfl
example : (List.range 2).map (fun j ↦ 3 * j + 1) = [1, 4] := rfl

example : (List.finRange 2).map (fun j : Fin 2 ↦ (Fin.castSucc j.rev).val) = [1, 0] := rfl

example : (List.range 2).map (fun j ↦ 3 * j - 1) = [0, 2] := rfl
example : (List.range 2).map (fun j ↦ 3 * j + 2) = [2, 5] := rfl
#guard 0 ∉ (finspan {3, 3 * 2 + 2}).gaps

/-- The `k = 2` case of `three_two_at_one`. -/
example {r₁ r₂ r₃ : ℕ} (h₂₁ : r₂ ≤ r₁) (h₃₂ : r₃ ≤ r₂) :
    (∑ᶠ m, lhsTerm 2 ![r₁, r₂, r₃] (finspan {3, 3 * 2 + 2}).gaps m).eval 1 =
      (∑ᶠ m, rhsTerm 2 ![r₁, r₂, r₃] m).eval 1 :=
  three_two_at_one 2 ![r₁, r₂, r₃] (Fin.antitone_iff_succ_le.mpr fun i ↦ by
    fin_cases i <;> simp_all)

end HJOA3.SumToSum.ThreeTwo
