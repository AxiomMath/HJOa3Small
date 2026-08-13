module

public import HJOA3.SumToSum.ThreeTwo.EightKernN1
public import HJOA3.SumToSum.ThreeTwo.EightRecLHS
public import HJOA3.SumToSum.ThreeTwo.EightRecRHS
public import HJOA3.SumToSum.ThreeTwo.EightResidualProof
public import HJOA3.WarnaarEight

/-!
# The `b = 8` case
-/

@[expose] public section

namespace HJOA3

open SumToSum.ThreeTwo

/-- `thm:sum` at `b = 8`, from `KernEightN1` alone. -/
theorem sumToSumEight_of_kernN1 (h : KernEightN1) : SumToSumEight :=
  sumToSumEight_of_rec (recEightLHS_of_kernN1 h) recEightRHS baseEight

/-- `thm:main` at `b = 8`, from `KernEightN1` and Warnaar `(1.10)`. -/
theorem conjecture_three_eight_of_kernN1 (h : KernEightN1) (hw : OuterChargeEight) :
    HJO.Conjecture 3 8 :=
  conjecture_three_eight_of_sumToSum (sumToSumEight_of_kernN1 h) hw

/-- `thm:sum` at `b = 8`. -/
theorem sumToSumEight : SumToSumEight :=
  sumToSumEight_of_kernN1 kernEightN1

/-- `thm:main` at `b = 8`, on Warnaar `(1.10)` alone. -/
theorem conjecture_three_eight_of_outerCharge (hw : OuterChargeEight) : HJO.Conjecture 3 8 :=
  conjecture_three_eight_of_sumToSum sumToSumEight hw

end HJOA3
