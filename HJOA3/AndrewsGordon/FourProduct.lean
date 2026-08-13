module

public import HJOA3.AndrewsGordon.Four
public import HJOA3.AndrewsGordon.Product

/-!
# `ThetaFour`: Warnaar's product side at modulus `7` is `P_{3,4}`
-/

@[expose] public section

namespace HJOA3.AndrewsGordon

/-- `ThetaFour`. -/
theorem thetaFour : ThetaFour := by
  rw [ThetaFour, plusRHS]
  norm_num
  exact rhs_eq_charge 3 4 7 2 2 3 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

end HJOA3.AndrewsGordon
