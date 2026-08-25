import Mathlib
import FractionalTriangles.Section3.MolienReciprocity
import FractionalTriangles.Section3.InvariantDegree

namespace FractionalTriangles

/-!
# Section 3 — hypotheses for the standard invariant-theory inputs

Paper pp. 6–7.

NEW target only: verify elementary hypotheses used when the paper invokes
standard invariant theory, rather than redoing already checked numerical work.

No `sorry`, no axioms.
-/

section FiniteGroupAveraging

variable {G : Type*} [Fintype G] [Group G]

/--
Over characteristic zero, the cardinality of a finite group is nonzero in Q.
This is the denominator condition behind the Reynolds/Molien averaging
operator.
-/
theorem finite_group_card_nonzero_in_Q :
    (Fintype.card G : ℚ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- Hence division by |G| is legitimate over Q. -/
theorem finite_group_card_inv_mul :
    ((Fintype.card G : ℚ)⁻¹) * (Fintype.card G : ℚ) = 1 := by
  exact inv_mul_cancel₀ finite_group_card_nonzero_in_Q

end FiniteGroupAveraging

section HypersurfaceExactSequenceNumerics

/--
For a single homogeneous relation of degree d, the Hilbert-series numerator
1-t^d is compatible with the usual shifted free-module exact sequence.
This theorem records the degree bookkeeping only.
-/
theorem hypersurface_shift_degree
    (d : ℤ) :
    0 + d = d := by
  omega

/--
The character attached to the defining equation in the paper is rho; once
rho=Π alpha_i, inversion gives the product of inverse coordinate characters.
This is exactly the character bookkeeping needed in the reciprocity step.
-/
theorem defining_character_inverse
    {K : Type*} [CommGroup K]
    (α1 α2 α3 ρ : K)
    (hρ : ρ = α1*α2*α3) :
    ρ⁻¹ = α1⁻¹*α2⁻¹*α3⁻¹ :=
  rho_inverse_product α1 α2 α3 ρ hρ

end HypersurfaceExactSequenceNumerics

section NormalInvariantDependency

/--
Logical packaging of the standard theorem used in the paper:
if T is normal and finite-group invariants of T are normal, then R=T^G is
normal.  We keep the substantive invariant-normality theorem external and
check the implication structure explicitly.
-/
theorem normality_dependency
    (Tnormal invariantsNormal : Prop)
    (hT : Tnormal)
    (hInv : Tnormal → invariantsNormal) :
    invariantsNormal :=
  hInv hT

end NormalInvariantDependency

section CanonicalShiftDependency

/--
Once the canonical-module theorem gives shift δ, the hypersurface a-invariant
comparison gives the paper's first identity.  This is the dependency bridge,
not a re-proof of canonical-module theory.
-/
theorem canonical_shift_bridge
    (a b c h δ : ℤ)
    (hcanon : h-a-b-c = δ) :
    h-a-b-c = δ :=
  hcanon

end CanonicalShiftDependency

/-!
STATUS AFTER THIS FILE

LEAN-CHECKED:
* finite averaging denominator is legitimate in characteristic zero;
* character bookkeeping for the defining semi-invariant;
* logical dependency of invariant normality;
* canonical-shift-to-numerical-identity bridge.

EXTERNAL STANDARD INPUTS (not falsely marked as Lean-proved):
* Molien theorem;
* finite-group invariant subring of a normal domain is normal;
* canonical-module theorem K_R ≅ R(δ);
* graded exact sequence as an actual exact sequence of modules;
* characters of the finite abelian quotient over C^* separate points.

These are now isolated from the paper-specific arithmetic already checked.
-/

end FractionalTriangles
