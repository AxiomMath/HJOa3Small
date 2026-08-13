module

public meta import QSeriesLib.NumberTheory.HJO.SumToSum.Small

/-!
# Faithfulness checks for the `b = 3k + 1` cases
-/

set_option linter.hashCommand false

open Finset NumericalSemigroup

namespace HJOA3.Test.ThreeOne

example : (finspan {3, 3 * 1 + 1}).gaps = {1, 2, 5} := rfl
example : (finspan {3, 3 * 2 + 1}).gaps = {1, 2, 4, 5, 8, 11} := rfl

example : (List.finRange 1).map (fun j : Fin 1 ↦ 6 * 1 - (3 * (j : ℕ) + 1)) = [5] := rfl
example : (List.finRange 2).map (fun j : Fin 2 ↦ 6 * 2 - (3 * (j : ℕ) + 1)) = [11, 8] := rfl

example : (List.finRange 6).map (fun i : Fin 6 ↦ (ThreeOne.toGaps 2 i).val) =
    [1, 4, 2, 5, 8, 11] := rfl

end HJOA3.Test.ThreeOne
