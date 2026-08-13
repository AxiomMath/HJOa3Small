module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The ternary star bound
-/

@[expose] public section

namespace HJOA3.QuadForm

/-- The ternary star bound. -/
theorem four_mul_star_le {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x y z : R) : 4 * (x * z + y * z) ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have key : 3 * (3 * (x ^ 2 + y ^ 2 + z ^ 2) - 4 * (x * z + y * z)) =
      (3 * x - 2 * z) ^ 2 + (3 * y - 2 * z) ^ 2 + z ^ 2 := by ring
  linarith [key, sq_nonneg (3 * x - 2 * z), sq_nonneg (3 * y - 2 * z), sq_nonneg z]

/-- The one-leaf case: a star with a single edge, against the *three*-variable diagonal. -/
theorem four_mul_single_le {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x y z : R) : 4 * (x * z) ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have key : 3 * (x ^ 2 + y ^ 2 + z ^ 2) - 4 * (x * z) =
      2 * (x - z) ^ 2 + x ^ 2 + z ^ 2 + 3 * y ^ 2 := by ring
  linarith [key, sq_nonneg (x - z), sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- `q3011` block bound. -/
theorem sq_le_four_mul_q3011 {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x y z : R) :
    x ^ 2 + y ^ 2 + z ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 - x * z - y * z) := by
  linarith [four_mul_star_le x y z]

/-- `q3001` block bound. -/
theorem sq_le_four_mul_q3001 {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x y z : R) : x ^ 2 + y ^ 2 + z ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 - x * z) := by
  linarith [four_mul_single_le x y z]

/-- `q1` block bound. -/
theorem sq_le_four_mul_q1 {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) :
    x ^ 2 ≤ 4 * x ^ 2 := by
  linarith [sq_nonneg x]

end HJOA3.QuadForm
