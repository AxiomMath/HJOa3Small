module

public import QSeriesLib.NumberTheory.HJO.SumToSum.Basic
public import QSeriesLib.NumberTheory.QTheory.Basic
public import HJOA3.SumToSum.ThreeTwo.EightBaseZero

/-!
# The `b = 8` identity over `ℤ[X]`
-/

@[expose] public section

open Finset Polynomial HJO HJO.SumToSum

namespace HJOA3

/-- A ring hom commutes with the extended `q`-binomial. -/
@[simp] theorem map_extendedQChoose {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (q : R) (n r : ℤ) : f (extendedQChoose q n r) = extendedQChoose (f q) n r := by
  unfold extendedQChoose
  split
  · exact map_qChoose (f := f)
  · exact map_zero f

namespace SumToSum.ThreeTwo

/-- `eightLHS` over `ℤ[X]`. -/
noncomputable def eightLHSInt (r₁ r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₁ + 1),
  ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
    X ^ (eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅).toNat *
      qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
      extendedQChoose X ((r₁ : ℤ) - n₂) ((n₅ : ℤ) - n₂)

/-- `eightRHS` over `ℤ[X]`. -/
noncomputable def eightRHSInt (r₁ r₂ r₃ : ℕ) : ℤ[X] :=
  ∑ m₁ ∈ range (2 * r₁ + 1), ∑ m₂ ∈ range (2 * r₁ + 1),
    X ^ (r₃ ^ 2 + ((r₁ ^ 2 + m₁ ^ 2 - r₁ * m₁) + (r₂ ^ 2 + m₂ ^ 2 - r₂ * m₂))) *
      qChoose X (r₁ - r₂ + m₂) m₁ * qChoose X (r₂ + r₃) m₂

theorem map_eightLHS (r₁ r₂ r₃ : ℕ) :
    Polynomial.mapRingHom (Nat.castRingHom ℤ) (eightLHS r₁ r₂ r₃) = eightLHSInt r₁ r₂ r₃ := by
  have hX : Polynomial.mapRingHom (Nat.castRingHom ℤ) (X : ℕ[X]) = X := Polynomial.map_X _
  simp only [eightLHS, eightLHSInt, map_sum, map_mul, map_pow, map_qChoose,
    map_extendedQChoose, hX]

theorem map_eightRHS (r₁ r₂ r₃ : ℕ) :
    Polynomial.mapRingHom (Nat.castRingHom ℤ) (eightRHS r₁ r₂ r₃) = eightRHSInt r₁ r₂ r₃ := by
  have hX : Polynomial.mapRingHom (Nat.castRingHom ℤ) (X : ℕ[X]) = X := Polynomial.map_X _
  simp only [eightRHS, eightRHSInt, map_sum, map_mul, map_pow, map_qChoose, hX]

/-- The `b = 8` identity is equivalent to its `ℤ[X]` transcription. -/
theorem eightLHS_eq_eightRHS_iff (r₁ r₂ r₃ : ℕ) :
    eightLHS r₁ r₂ r₃ = eightRHS r₁ r₂ r₃ ↔ eightLHSInt r₁ r₂ r₃ = eightRHSInt r₁ r₂ r₃ := by
  rw [← map_eightLHS, ← map_eightRHS]
  exact ⟨fun h ↦ by rw [h],
    fun h ↦ Polynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective h⟩

/-- `BaseEight` follows from the level-`r₂ + 1` identity over `ℤ[X]`. -/
theorem baseEight_of_succ_int
    (h : ∀ r₂ r₃ : ℕ, r₃ ≤ r₂ → eightLHSInt (r₂ + 1) r₂ r₃ = eightRHSInt (r₂ + 1) r₂ r₃) :
    BaseEight :=
  baseEight_of_succ fun r₂ r₃ h₃ ↦ (eightLHS_eq_eightRHS_iff _ _ _).2 (h r₂ r₃ h₃)

/-- `eightLHSInt` with no extended `q`-binomial, the `ℤ[X]` form of `eightLHS_eq_guarded`. -/
theorem eightLHSInt_eq_guarded (r₁ r₂ r₃ : ℕ) (h₂₁ : r₂ ≤ r₁) :
    eightLHSInt r₁ r₂ r₃ =
      ∑ n₂ ∈ range (r₂ + 1), ∑ n₅ ∈ range (r₁ + 1),
      ∑ n₁ ∈ range (r₃ + 1), ∑ n₄ ∈ range (r₃ + 1),
        X ^ (eightExp r₁ r₂ r₃ n₁ n₂ n₄ n₅).toNat *
          qChoose X n₄ n₁ * qChoose X r₃ n₄ * qChoose X r₂ n₂ *
          (if n₂ ≤ n₅ then qChoose X (r₁ - n₂) (n₅ - n₂) else 0) := by
  have hX : Polynomial.mapRingHom (Nat.castRingHom ℤ) (X : ℕ[X]) = X := Polynomial.map_X _
  rw [← map_eightLHS, eightLHS_eq_guarded r₁ r₂ r₃ h₂₁]
  simp only [map_sum, map_mul, map_pow, map_qChoose, apply_ite, map_zero, hX]

end SumToSum.ThreeTwo

end HJOA3
