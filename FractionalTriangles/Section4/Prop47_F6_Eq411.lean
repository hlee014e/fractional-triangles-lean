import Mathlib

namespace FractionalTriangles
namespace Section4

/--
Arithmetic verification of equation (4.11) in Proposition 4.7, f₆, W = 1 case.

Paper data:
  A = e₀(d t₀ + 1)/a,
  B = t₀,
  C = e₀,
  h = d e₀ t₀ + e₀ + t₀,
  δ = h - A - B - C.

Using the orbifold adjunction rearrangement
  2g = δ h/(ABC) - 1 + 1/A + 1/B + 1/C,
Lean verifies
  2g = d(a-1) + a/e₀ - 1.
-/
theorem f6_eq411
    (a d e₀ t₀ : ℕ)
    (ha : 0 < a)
    (he₀ : 0 < e₀)
    (ht₀ : 0 < t₀) :
    let A : ℚ := (e₀ : ℚ) * ((d : ℚ) * (t₀ : ℚ) + 1) / (a : ℚ)
    let B : ℚ := (t₀ : ℚ)
    let C : ℚ := (e₀ : ℚ)
    let h : ℚ := (d : ℚ) * (e₀ : ℚ) * (t₀ : ℚ) + (e₀ : ℚ) + (t₀ : ℚ)
    let δ : ℚ := h - A - B - C
    δ * h / (A * B * C) - 1 + 1 / A + 1 / B + 1 / C
      = (d : ℚ) * ((a : ℚ) - 1) + (a : ℚ) / (e₀ : ℚ) - 1 := by
  have ha0 : (a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  have he0 : (e₀ : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt he₀)
  have ht0 : (t₀ : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ht₀)
  have hdt1 : (d : ℚ) * (t₀ : ℚ) + 1 ≠ 0 := by
    positivity

  dsimp
  field_simp [ha0, he0, ht0, hdt1]
  ring

end Section4
end FractionalTriangles
