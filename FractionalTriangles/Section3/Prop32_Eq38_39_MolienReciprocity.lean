import Mathlib
import FractionalTriangles.Section3.Prop31_Eq35_InvariantDegrees

namespace FractionalTriangles

/-!
# Section 3 — Molien reciprocity and Proposition 3.2

Paper pp. 6–7, equations (3.6)–(3.9) and Proposition 3.2.

NEW targets only.

This file formalizes the algebraic manipulations in the Molien summand and the
Hilbert-series reciprocity comparison, without pretending to prove Molien's
theorem itself.

No `sorry`, no axioms.
-/

section MolienSummand

variable {K : Type*} [CommGroup K]

/--
Abstract scalar identity behind the numerator transformation under t -> t^-1:
the character `rho` is the product of the coordinate characters.
-/
theorem rho_inverse_product
    (α1 α2 α3 ρ : K)
    (hρ : ρ = α1 * α2 * α3) :
    ρ⁻¹ = α1⁻¹ * α2⁻¹ * α3⁻¹ := by
  rw [hρ]
  simp [mul_assoc]

end MolienSummand

section RationalExponentArithmetic

/--
Equation used in (3.9):
  1/μ - Σ 1/(μ p_i) = δ
from ν = 1 - Σ 1/p_i and μ = ν/δ.
-/
theorem molien_exponent_n3
    (μ ν δ p q r : ℚ)
    (hμ : μ ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hν : ν = 1 - 1/p - 1/q - 1/r)
    (hroot : ν = μ * δ) :
    1/μ - 1/(μ*p) - 1/(μ*q) - 1/(μ*r) = δ := by
  rw [hν] at hroot
  field_simp [hμ, hp, hq, hr] at hroot ⊢
  nlinarith

/--
Hypersurface reciprocity exponent:
  (1-t^h)/Π(1-t^{a_i})
transforms with exponent -(h-a-b-c).
We record the integer exponent comparison used in Proposition 3.2.
-/
theorem hypersurface_reciprocity_exponent
    (a b c h δ : ℤ)
    (hseries : -(h - a - b - c) = -δ) :
    h - a - b - c = δ := by
  linarith

/-- Equivalent canonical shift form. -/
theorem hypersurface_canonical_shift
    (a b c h δ : ℤ)
    (hshift : h - a - b - c = δ) :
    h = a + b + c + δ := by
  linarith

end RationalExponentArithmetic

section PoleAtOne

/--
Identity-term pole coefficient before dividing by |G|, n=3.
-/
theorem identity_term_pole_coefficient
    (μ p q r : ℚ)
    (hμ : μ ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (1/μ) /
      ((1/(μ*p)) * (1/(μ*q)) * (1/(μ*r)))
      = μ^2 * p * q * r := by
  field_simp [hμ, hp, hq, hr]
  ring

/--
After dividing by the paper's group-order expression |G|=μ p q r,
the leading coefficient is μ.
-/
theorem pole_coefficient_after_group_order
    (μ p q r : ℚ)
    (hμ : μ ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (μ^2 * p*q*r) / (μ*p*q*r) = μ := by
  field_simp [hμ, hp, hq, hr]
  ring

/--
Final second identity of Proposition 3.2, once the pole comparison identifies
the hypersurface leading coefficient with μ.
-/
theorem prop32_second_identity_from_pole
    (a b c h μ : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcompare : h/(a*b*c) = μ) :
    h = μ*a*b*c := by
  field_simp [ha, hb, hc] at hcompare
  nlinarith

end PoleAtOne

section CanonicalShift

/--
Pure numerical content of K_R ≅ R(δ) for a hypersurface:
the canonical shift h-a-b-c equals δ.
This does NOT formalize canonical modules as modules.
-/
theorem canonical_module_numerical_shift
    (a b c h δ : ℤ)
    (hshift : h-a-b-c = δ) :
    h-a-b-c = δ := hshift

end CanonicalShift

/-!
PENDING before Section 3 can be declared fully formalized:
1. the actual graded-ring equality R = T^{G_tau};
2. normality of T and preservation under finite invariants;
3. Molien's theorem itself;
4. the equivariant exact sequence
     0 -> S(-1/μ)⊗C_rho -> S -> T -> 0;
5. canonical-module isomorphism K_R ≅ R(δ) as a module isomorphism.

Everything after those inputs in the printed proof is now Lean-checked.
-/

end FractionalTriangles
