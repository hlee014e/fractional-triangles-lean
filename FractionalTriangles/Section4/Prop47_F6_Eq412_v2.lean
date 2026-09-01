import Mathlib

namespace FractionalTriangles
namespace Section4

/--
Arithmetic verification of equation (4.12) in Proposition 4.7, f₆, W > 1 case.

Paper data:
  A = 1,
  B = W t,
  C = W e,
  h = W (e t + e + t),
  δ = h - A - B - C = W e t - 1.

The three nontrivial stacky orders are
  (W t, W e, W).

Using
  2g = δ h/(ABC) - 1 + 1/(Wt) + 1/(We) + 1/W,
Lean verifies
  2g = e t + e + t - 1.
-/
theorem f6_eq412
    (W e t : ℕ)
    (hW : 0 < W)
    (he : 0 < e)
    (ht : 0 < t) :
    let A : ℚ := 1
    let B : ℚ := (W : ℚ) * (t : ℚ)
    let C : ℚ := (W : ℚ) * (e : ℚ)
    let h : ℚ := (W : ℚ) * ((e : ℚ) * (t : ℚ) + (e : ℚ) + (t : ℚ))
    let δ : ℚ := h - A - B - C
    δ * h / (A * B * C)
      - 1
      + 1 / ((W : ℚ) * (t : ℚ))
      + 1 / ((W : ℚ) * (e : ℚ))
      + 1 / (W : ℚ)
      =
      (e : ℚ) * (t : ℚ) + (e : ℚ) + (t : ℚ) - 1 := by
  have hW0 : (W : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hW)
  have he0 : (e : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt he)
  have ht0 : (t : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ht)

  dsimp
  field_simp [hW0, he0, ht0]
  ring

/--
Positivity of the right-hand side of (4.12) for e,t >= 1.
-/
theorem f6_eq412_positive
    (e t : ℕ)
    (he : 0 < e)
    (ht : 0 < t) :
    0 < (e : ℤ) * (t : ℤ) + (e : ℤ) + (t : ℤ) - 1 := by
  have heZ : 0 < (e : ℤ) := by
    exact_mod_cast he
  have htZ : 0 < (t : ℤ) := by
    exact_mod_cast ht
  have hetZ : 0 < (e : ℤ) * (t : ℤ) := mul_pos heZ htZ
  omega

end Section4
end FractionalTriangles
