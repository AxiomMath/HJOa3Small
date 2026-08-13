module

public import HJOA3.AndrewsGordon.Product

/-!
# Warnaar's product side at modulus `8` is `P_{3,5}`
-/

@[expose] public section

namespace HJOA3.AndrewsGordon

/-- Warnaar's theta quotient at modulus `8` is HJO's charge `P_{3,5}`. -/
theorem minusRHS_one_eq_charge : minusRHS 1 = HJO.charge 3 5 := by
  rw [minusRHS]
  norm_num
  exact rhs_eq_charge 3 5 8 2 3 3 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

end HJOA3.AndrewsGordon
