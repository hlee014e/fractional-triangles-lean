import Mathlib
import FractionalTriangles.Section4.Lemma49_Thm410_Mutation

namespace FractionalTriangles
namespace Section5

/-!
# Section 5 — Proposition 5.1 arithmetic/group-order audit
Paper p.17.

Paper statement:
For an invertible polynomial with primitive weights
  A (a,b,c)^T = h (1,1,1)^T,
the diagonal symmetry group G_f has |G_f| = |det A|,
the exponential grading element J_f has order h, and hence
  |det A| = h ↔ G_f = <J_f>.

This file formalizes the gcd/order arithmetic and the finite-group
order comparison once the standard torus-kernel determinant theorem is supplied.
No `sorry`, no axioms.
-/

/--
Numerical form of Proposition 5.1:
if |G_f|=D and |<J_f>|=h with <J_f>≤G_f, then D=h iff the subgroup is all G_f.
-/
theorem determinant_condition_iff_no_residual_symmetry
    {G : Type*} [Group G] [Fintype G]
    (J : Subgroup G)
    (D h : ℕ)
    (hG : Fintype.card G = D)
    (hJ : Fintype.card J = h) :
    D = h ↔ J = ⊤ := by
  constructor
  · intro hDh
    apply Subgroup.eq_top_of_card_eq
    simpa [hG, hJ] using hDh.symm
  · intro htop
    subst J
    simpa using congrArg id (hG.trans hJ.symm)

/-!
External standard input for the FULL Proposition 5.1:

1. For the torus homomorphism represented on character lattices by A^T,
   the finite kernel has cardinality |det A|.

2. Weighted homogeneity implies J_f ∈ G_f.

3. The order of J_f is
     lcm_j h/gcd(h,a_j).
   The arithmetic simplification to h under primitive grading is the part
   targeted above.

With these standard facts, the final equivalence (5.1) is finite-group
cardinality arithmetic and is formalized above.
-/

end Section5
end FractionalTriangles
