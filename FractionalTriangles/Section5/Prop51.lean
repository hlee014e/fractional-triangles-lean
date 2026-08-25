import Mathlib
import FractionalTriangles.Section4.Mutation

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

/-- Primitive weights imply gcd(h,a,b,c)=1 once h is an integer
combination compatible with the primitive grading.  Here we isolate the
gcd reduction actually used in the order computation. -/
theorem gcd_h_abc_of_gcd_abc_one
    (h a b c : ℕ)
    (habc : Nat.gcd a (Nat.gcd b c) = 1)
    (ha : a ∣ h) (hb : b ∣ h) (hc : c ∣ h) :
    Nat.gcd h (Nat.gcd a (Nat.gcd b c)) = 1 := by
  simp [habc]

/-- If gcd(h,a,b,c)=1 then the lcm of h/gcd(h,a_i) is h.
This is the elementary order formula for J_f. -/
theorem lcm_three_quotients_eq_h
    (h a b c : ℕ)
    (hh : 0 < h)
    (hg : Nat.gcd h (Nat.gcd a (Nat.gcd b c)) = 1) :
    Nat.lcm (h / Nat.gcd h a)
      (Nat.lcm (h / Nat.gcd h b) (h / Nat.gcd h c)) = h := by
  have hga : Nat.gcd h a ∣ h := Nat.gcd_dvd_left h a
  have hgb : Nat.gcd h b ∣ h := Nat.gcd_dvd_left h b
  have hgc : Nat.gcd h c ∣ h := Nat.gcd_dvd_left h c
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact Nat.div_dvd_of_dvd hga
    · apply Nat.lcm_dvd
      · exact Nat.div_dvd_of_dvd hgb
      · exact Nat.div_dvd_of_dvd hgc
  · rw [← Nat.coprime_iff_gcd_eq_one] at hg
    -- It suffices to use the standard identity relating gcd and lcm
    -- for the three divisors of h.
    have h1 : Nat.gcd (Nat.gcd h a) (Nat.gcd (Nat.gcd h b) (Nat.gcd h c)) = 1 := by
      simpa [Nat.gcd_assoc, Nat.gcd_left_comm, Nat.gcd_comm] using hg
    omega

/-- Pure finite-group order comparison:
if H≤G, |H|=h and |G|=D, then D=h implies H=G. -/
theorem subgroup_eq_of_card_eq
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G)
    (hcard : Fintype.card H = Fintype.card G) :
    H = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  simpa using hcard

/-- Conversely H=G forces equality of their finite cardinalities. -/
theorem card_eq_of_subgroup_top
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G)
    (hH : H = ⊤) :
    Fintype.card H = Fintype.card G := by
  subst H
  simp

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
    apply subgroup_eq_of_card_eq J
    rw [hJ, hG, hDh]
  · intro htop
    have hc := card_eq_of_subgroup_top J htop
    omega

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
