module

public import HJOA3.AndrewsGordon.Product

/-!
# Warnaar's product side at modulus `10` is `P_{3,7}`
-/

@[expose] public section

namespace HJOA3.AndrewsGordon

/-- Warnaar's theta quotient at modulus `10` is HJO's charge `P_{3,7}`. -/
theorem plusRHS_one_eq_charge : plusRHS 1 = HJO.charge 3 7 := by
  rw [plusRHS]
  norm_num
  exact rhs_eq_charge 3 7 10 3 3 4 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

end HJOA3.AndrewsGordon
