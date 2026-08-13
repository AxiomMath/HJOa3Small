module

public import QSeriesLib.NumberTheory.HJO.Defs

/-!
# `HJO.negR` is periodic with period `a + b`
-/

@[expose] public section

namespace HJO

/-- `negR` is invariant under one shift by its period. -/
theorem negR_add_right (a b n : ℕ) : negR a b (n + (a + b)) = negR a b n := by
  unfold negR
  congr 2
  · congr 1
    push_cast
    rw [show (a : ℤ) * ((n : ℤ) + ((a : ℤ) + (b : ℤ))) = (a : ℤ) * n + ((a + b : ℕ) : ℤ) * a by
      push_cast; ring, Int.add_mul_bmod_self_left]
  · simp [Nat.dvd_add_self_right]

/-- `negR` is invariant under any number of shifts by its period. -/
theorem negR_add_mul_right (a b n t : ℕ) : negR a b (n + (a + b) * t) = negR a b n := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, negR_add_right, ih]

theorem negR_mul_add (a b t j : ℕ) : negR a b ((a + b) * t + j) = negR a b j := by
  rw [Nat.add_comm, negR_add_mul_right]

end HJO
