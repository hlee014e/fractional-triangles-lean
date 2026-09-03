import Mathlib

namespace FractionalTriangles
namespace Section5

/-!

# Section 5 — Proposition 5.1 Lean audit

This file records the part of Proposition 5.1 that is currently
formalized in Lean.

Lean verifies the following two statements.

1. Finite-group order comparison.

For a finite group G and subgroup J, if

    Nat.card G = D
    Nat.card J = h,

then

    D = h ↔ J = ⊤.

In the application to Proposition 5.1, this is the final group-theoretic
step after the identities

    |G_f| = |det A|
    |<J_f>| = h

have been supplied.

2. Arithmetic core of the grading-element order computation.

Under

    gcd(h, gcd(a, gcd(b,c))) = 1,

Lean proves

    lcm(h/gcd(h,a),
        lcm(h/gcd(h,b), h/gcd(h,c))) = h.

This is the number-theoretic identity underlying ord(J_f) = h.

The following parts of Proposition 5.1 are NOT claimed to be formalized
in this file:

* the torus-kernel/character-lattice theorem |G_f| = |det A|;
* the construction of the complex grading element J_f;
* the proof J_f ∈ G_f from weighted homogeneity;
* the identification of the order of each complex root-of-unity
  coordinate with h/gcd(h,a_i);
* therefore the complete statement ord(J_f) = h as a theorem about the
  actual complex diagonal symmetry group.

Thus this file verifies the arithmetic and finite-group core of
Proposition 5.1, conditional on the standard torus-kernel and
root-of-unity identifications.

No `sorry`. No axioms.

-/

/--
Numerical form of Proposition 5.1:
if |G_f|=D and |<J_f>|=h with <J_f>≤G_f, then D=h iff the subgroup is all G_f.
-/
theorem determinant_condition_iff_no_residual_symmetry
    {G : Type*} [Group G] [Finite G]
    (J : Subgroup G)
    (D h : ℕ)
    (hG : Nat.card G = D)
    (hJ : Nat.card J = h) :
    D = h ↔ J = ⊤ := by
  constructor
  · intro hDh
    apply Subgroup.eq_top_of_card_eq
    calc
      Nat.card J = h := hJ
      _ = D := hDh.symm
      _ = Nat.card G := hG.symm
  · intro htop
    subst J
    calc
      D = Nat.card G := hG.symm
      _ = Nat.card (⊤ : Subgroup G) := by
        rw [Subgroup.card_top]
      _ = h := hJ

end Section5
end FractionalTriangles

namespace FractionalTriangles
namespace Section5

/--
Arithmetic core of the order computation in Proposition 5.1.

For primitive weights, the order of the grading element is

  lcm (h/gcd(h,a), h/gcd(h,b), h/gcd(h,c)) = h.
-/
theorem prop51_lcm_coordinate_orders
    (h a b c : ℕ)
    (hg : Nat.gcd h (Nat.gcd a (Nat.gcd b c)) = 1) :
    Nat.lcm (h / Nat.gcd h a)
      (Nat.lcm (h / Nat.gcd h b)
        (h / Nat.gcd h c)) = h := by

  have ha : Nat.gcd h a ∣ h :=
    Nat.gcd_dvd_left h a

  have hb : Nat.gcd h b ∣ h :=
    Nat.gcd_dvd_left h b

  have hc : Nat.gcd h c ∣ h :=
    Nat.gcd_dvd_left h c

  have hbc :
      Nat.gcd (Nat.gcd h b) (Nat.gcd h c) ∣ h := by
    exact dvd_trans
      (Nat.gcd_dvd_left (Nat.gcd h b) (Nat.gcd h c))
      hb

  rw [Nat.div_lcm_eq_div_gcd hb hc]
  rw [Nat.div_lcm_eq_div_gcd ha hbc]

  have hfour :
      Nat.gcd (Nat.gcd h a)
        (Nat.gcd (Nat.gcd h b) (Nat.gcd h c)) = 1 := by
    simpa [Nat.gcd_assoc, Nat.gcd_left_comm, Nat.gcd_comm] using hg

  rw [hfour]
  simp

end Section5
end FractionalTriangles
