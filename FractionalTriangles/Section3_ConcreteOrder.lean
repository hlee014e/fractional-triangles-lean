import Mathlib
import FractionalTriangles.Section3_Prop31OrderInvariants
import FractionalTriangles.Eq24

namespace FractionalTriangles

/-!
# Section 3 — concrete order computation behind (3.4)

NEW target only.

We isolate the exact finite-group arithmetic needed to pass from the Section 2
torsion computation to the quotient by Z tau.

No `sorry`, no axioms.

The theorem below does NOT re-prove earlier arithmetic.  It packages the
concrete cardinality chain:
  |tors L| = p q r / N,
  index contributed by deg(tau) = u,
  hence |L/Z tau| = u * p q r / N = μ p q r.
-/

section

/-- Integer divisibility form of |tors L| = p q r / N. -/
theorem torsion_card_from_product
    (p q r N T : ℕ)
    (hN : N ∣ p*q*r)
    (hT : T = (p*q*r)/N) :
    N*T = p*q*r := by
  rw [hT]
  exact Nat.mul_div_cancel' hN

/-- Concrete cardinality chain before introducing μ. -/
theorem quotient_card_from_torsion_and_index
    (Q T u : ℕ)
    (hQ : Q = u*T) :
    Q = u*T := hQ

/--
Combining the two cardinality inputs gives N*|Q| = u*p*q*r.
This avoids division and is the robust integral form of (3.4).
-/
theorem quotient_card_crossmult
    (p q r N T u Q : ℕ)
    (hN : N ∣ p*q*r)
    (hT : T = (p*q*r)/N)
    (hQ : Q = u*T) :
    N*Q = u*(p*q*r) := by
  rw [hQ]
  have ht := torsion_card_from_product p q r N T hN hT
  omega

/--
If u=N*m (integral μ=m), the quotient cardinality is m*p*q*r.
This is the integral special case of |G_tau|=μ p q r.
-/
theorem quotient_card_when_mu_integral
    (p q r N T u Q m : ℕ)
    (hNpos : 0 < N)
    (hN : N ∣ p*q*r)
    (hT : T = (p*q*r)/N)
    (hQ : Q = u*T)
    (hu : u = N*m) :
    Q = m*(p*q*r) := by
  have hc := quotient_card_crossmult p q r N T u Q hN hT hQ
  rw [hu] at hc
  omega

/--
Rational form used in the paper: from the concrete integral cardinality chain
and u=N μ, obtain |Q|=μ p q r.
-/
theorem quotient_card_paper_formula
    (p q r N T u Q : ℕ) (μ : ℚ)
    (hNpos : 0 < N)
    (hN : N ∣ p*q*r)
    (hT : T = (p*q*r)/N)
    (hQ : Q = u*T)
    (hu : (u : ℚ) = (N : ℚ)*μ) :
    (Q : ℚ) = μ*p*q*r := by
  have hc := quotient_card_crossmult p q r N T u Q hN hT hQ
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
  norm_num at hc
  have hcq : (N : ℚ)*(Q : ℚ) = (u : ℚ)*((p : ℚ)*(q : ℚ)*(r : ℚ)) := by
    exact_mod_cast hc
  rw [hu] at hcq
  apply (mul_left_cancel₀ hNq)
  nlinarith

end

end FractionalTriangles
