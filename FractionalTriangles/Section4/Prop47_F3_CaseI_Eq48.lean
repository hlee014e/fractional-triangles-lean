import Mathlib

namespace FractionalTriangles
namespace Section4

/--
Case (I) in Proposition 4.7, f₃-branch.

After the paper has reached
  (A,B,C) = (e₀ U, a₀ U, 1),
  h = a₀ U (2 e₀ + 1),
with stacky orders (e₀ U, U, U),
this theorem verifies the exact adjunction simplification (4.8)
and its positivity.

The geometric assertion that these are exactly the three stacky orders
comes from Lemma 4.5 and is not formalized here.
-/
theorem f3_caseI_eq48
    (a₀ e₀ U : ℚ)
    (ha₀ : 1 ≤ a₀)
    (he₀ : 1 ≤ e₀)
    (hU : 0 < U) :
    let A := e₀ * U
    let B := a₀ * U
    let h := a₀ * U * (2 * e₀ + 1)
    let δ := h - A - B - 1
    let two_g :=
      δ * h / (A * B)
        - 1
        + 1 / (e₀ * U)
        + 1 / U
        + 1 / U
    two_g = 2 * (2 * a₀ * e₀ + a₀ - e₀ - 1)
      ∧
    two_g = 2 * ((a₀ - 1) * (2 * e₀ + 1) + e₀)
      ∧
    0 < two_g := by
  dsimp
  have ha₀0 : a₀ ≠ 0 := by linarith
  have he₀0 : e₀ ≠ 0 := by linarith
  have hU0 : U ≠ 0 := ne_of_gt hU

  have hEq :
      ((a₀ * U * (2 * e₀ + 1) - e₀ * U - a₀ * U - 1)
          * (a₀ * U * (2 * e₀ + 1))
          / ((e₀ * U) * (a₀ * U))
        - 1
        + 1 / (e₀ * U)
        + 1 / U
        + 1 / U)
        =
      2 * ((a₀ - 1) * (2 * e₀ + 1) + e₀) := by
    field_simp [ha₀0, he₀0, hU0]
    ring

  constructor
  · rw [hEq]
    ring
  constructor
  · exact hEq
  · rw [hEq]
    have h1 : 0 ≤ a₀ - 1 := by linarith
    have h2 : 0 < 2 * e₀ + 1 := by linarith
    have h3 : 0 ≤ (a₀ - 1) * (2 * e₀ + 1) := by
      exact mul_nonneg h1 (le_of_lt h2)
    linarith

end Section4
end FractionalTriangles
