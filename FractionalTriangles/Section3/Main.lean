import FractionalTriangles.Section3.ProofAudit
import FractionalTriangles.Section3.Prop31Next
import FractionalTriangles.Section3.Prop31Relations
import FractionalTriangles.Section3.Prop31_Eq33_GradingCharacters
import FractionalTriangles.Section3.Prop31_Eq33_Characterization
import FractionalTriangles.Section3.Prop31OrderInvariants
import FractionalTriangles.Section3.Prop31_Eq34_Order
import FractionalTriangles.Section3.Prop31_Eq35_InvariantDegrees
import FractionalTriangles.Section3.Prop32_Eq38_39_MolienReciprocity

namespace FractionalTriangles

/-!
# Section 3 — consolidated verification entry point

Paper pp. 6–7.

This file is the single entry point for all Section 3 Lean verification
completed so far.  The imported component files are intentionally retained
for this consolidation build; after this builds, they can later be physically
merged/de-duplicated without changing the mathematical verification.

## Lean-checked paper-specific content
* Proposition 3.1 / (3.3): actual-character characterization, including
  p_i-power relations from the concrete grading group, product relation,
  rho^u=1, and the coprime converse.
* (3.4): finite quotient/cardinality mechanisms and the full arithmetic chain
  to |G_tau| = mu p q r.
* (3.5): invariant-degree criterion modulo the standard character-separation
  theorem.
* (3.8)–(3.9), Proposition 3.2: reciprocity exponent arithmetic, pole
  coefficient arithmetic, and the two numerical hypersurface identities.

## Explicit external dependencies
The following substantial standard results are NOT claimed as Lean-proved:
* finite abelian characters over C^* separate points;
* the actual graded-ring equality R = T^{G_tau} as ring objects;
* Molien's theorem;
* the equivariant exact sequence producing the Molien numerator;
* normality of finite invariant subrings;
* K_R ≅ R(delta) as a canonical-module isomorphism.

Thus this is a Lean-assisted paper verification, not a claim that all
invariant-theory infrastructure has been formalized from foundations.
-/

end FractionalTriangles
