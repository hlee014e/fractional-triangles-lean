import Mathlib

/-!
# Lemma 4.9 — C2F, Y = Z = 1

For

  g = x^a y + y^b + z^c,

put

  e = b - 1,
  r = gcd(a,e),
  s = gcd(b,c).

In the subcase Y = Z = 1, we also have X = 1.

The exactly-three-stacky-points condition becomes

  1 + r + s = 3.

Since r,s are positive gcds, this forces r=s=1.

Equation (4.18) then reduces at genus zero to

  q - 1 = 0,

hence q=1.
-/

namespace FractionalTriangles.Section4.Lemma49C2FBothLinesActive

/--
If `1 + r + s = 3` and `r,s >= 1`, then `r=s=1`.
-/
theorem count_three_forces_r_s_one
    (r s : ℕ)
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hcount : 1 + r + s = 3) :
    r = 1 ∧ s = 1 := by
  omega

/--
When X=Y=Z=1, the parenthesis in equation (4.18)
reduces to 1.
-/
theorem eq418_all_present_reduces
    (a c ce q : ℕ) :
    (q : ℚ) *
        (1
          - (1 - 1 : ℚ) / (a : ℚ)
          - (1 - 1 : ℚ) / (c : ℚ)
          - (1 - 1 : ℚ) / (ce : ℚ))
        - 1
      =
    (q : ℚ) - 1 := by
  ring

/--
Thus genus zero forces q=1.
-/
theorem q_eq_one
    (a c ce q : ℕ)
    (hgenus :
      (q : ℚ) *
          (1
            - (1 - 1 : ℚ) / (a : ℚ)
            - (1 - 1 : ℚ) / (c : ℚ)
            - (1 - 1 : ℚ) / (ce : ℚ))
          - 1
        = 0) :
    q = 1 := by
  have hsimp :
      (q : ℚ) *
          (1
            - (1 - 1 : ℚ) / (a : ℚ)
            - (1 - 1 : ℚ) / (c : ℚ)
            - (1 - 1 : ℚ) / (ce : ℚ))
          - 1
        =
      (q : ℚ) - 1 := by
    exact eq418_all_present_reduces a c ce q

  have hqQ : (q : ℚ) = 1 := by
    linarith

  exact_mod_cast hqQ

end FractionalTriangles.Section4.Lemma49C2FBothLinesActive
