import Mathlib

/-!
# Lemma 4.9 — FFF, all three coordinate pairs active

Paper case:

  g = x^a + y^b + z^c.

Equation (4.15) is

  2g =
    q * (1 - 1/a - 1/b - 1/c
           + sum over active pairs of the corresponding reciprocal)
    - 1.

If all three pairs are active, the cyclic contribution is

  1/c + 1/b + 1/a,

so (4.15) reduces to

  2g = q - 1.

Since the coarse genus is zero, q = 1.

The coordinate-stratum justification for which terms occur was already
audited in Lemma 4.8.  This file checks the algebraic reduction and the
genus-zero consequence.
-/

namespace FractionalTriangles.Section4.Lemma49FFFAllThreeActive

/--
In the FFF case, when all three coordinate pairs are active,
the right-hand side of equation (4.15) simplifies to `q - 1`.
-/
theorem eq415_all_three_active
    (a b c q : ℕ) :
    (q : ℚ) *
        (1
          - 1 / (a : ℚ)
          - 1 / (b : ℚ)
          - 1 / (c : ℚ)
          + 1 / (c : ℚ)
          + 1 / (b : ℚ)
          + 1 / (a : ℚ))
        - 1
      =
    (q : ℚ) - 1 := by
  ring

/--
FFF, all three pairs active:

equation (4.15) together with genus zero forces `q = 1`.
-/
theorem q_eq_one_of_all_three_active
    (a b c q : ℕ)
    (hgenus :
      (q : ℚ) *
          (1
            - 1 / (a : ℚ)
            - 1 / (b : ℚ)
            - 1 / (c : ℚ)
            + 1 / (c : ℚ)
            + 1 / (b : ℚ)
            + 1 / (a : ℚ))
          - 1
        = 0) :
    q = 1 := by
  have hsimp :
      (q : ℚ) *
          (1
            - 1 / (a : ℚ)
            - 1 / (b : ℚ)
            - 1 / (c : ℚ)
            + 1 / (c : ℚ)
            + 1 / (b : ℚ)
            + 1 / (a : ℚ))
          - 1
        =
      (q : ℚ) - 1 :=
    eq415_all_three_active a b c q

  have hq_rat : (q : ℚ) = 1 := by
    linarith

  exact_mod_cast hq_rat

end FractionalTriangles.Section4.Lemma49FFFAllThreeActive
