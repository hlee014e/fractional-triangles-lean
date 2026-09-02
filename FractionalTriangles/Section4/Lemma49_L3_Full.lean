import Mathlib

/-!
# Lemma 4.9 — L3 case

For

  g = x^a y + y^b z + z^c x,

the raw weight system and its weighted homogeneity were already
verified in the Lemma 4.8 audit.

Lemma 4.8 also verifies that the only coordinate-stratum
contributions are the three coordinate vertices.

For the L3 case, substitution of their three stabilizer orders
into the adjunction formula gives equation (4.22):

  2g = q - 1.

Hence genus zero forces q=1.
-/

namespace FractionalTriangles.Section4.Lemma49L3

/--
Equation (4.22) with genus zero forces q=1.
-/
theorem genus_zero_forces_q_one
    (q : ℕ)
    (h422 : (q : ℚ) - 1 = 0) :
    q = 1 := by
  have hqQ : (q : ℚ) = 1 := by
    linarith
  exact_mod_cast hqQ

/--
Arithmetic conclusion of the L3 case of Lemma 4.9.
-/
theorem l3_conclusion
    (q : ℕ)
    (h422 : (q : ℚ) - 1 = 0) :
    q = 1 := by
  exact genus_zero_forces_q_one q h422

end FractionalTriangles.Section4.Lemma49L3
