import Mathlib

/-!
# Lemma 4.9 — FFF, two active coordinate pairs

This audits the arithmetic step leading to equation (4.16).

In the two-active-pair case, equation (4.15) reduces at genus zero to

  q * (1 - 1/a) - 1 = 0.

For integers a >= 2 and q > 1 this forces a = q = 2.

Then gcd(a,b)=2 forces b to be even.  Finally, after a=q=2,
D_bc = 1 becomes gcd(b,c)=1.
-/

namespace FractionalTriangles.Section4.Lemma49FFFTwoActive

/--
The genus-zero equation in the FFF two-active-pair case
forces `a = q = 2`.
-/
theorem two_active_forces_a_q_two
    (a q : ℕ)
    (ha : 2 ≤ a)
    (hq : 2 ≤ q)
    (h :
      (q : ℚ) * (1 - 1 / (a : ℚ)) - 1 = 0) :
    a = 2 ∧ q = 2 := by
  have haQ : (2 : ℚ) ≤ (a : ℚ) := by
    exact_mod_cast ha
  have hqQ : (2 : ℚ) ≤ (q : ℚ) := by
    exact_mod_cast hq
  have ha0 : (a : ℚ) ≠ 0 := by
    positivity

  field_simp [ha0] at h

  have ha_eq : (a : ℚ) = 2 := by
    nlinarith
  have hq_eq : (q : ℚ) = 2 := by
    nlinarith

  constructor
  · exact_mod_cast ha_eq
  · exact_mod_cast hq_eq

/--
If gcd(a,b)=2 and the previous step gives a=2,
then b is even.
-/
theorem b_even_of_gcd_eq_two
    (a b : ℕ)
    (ha : a = 2)
    (hab : Nat.gcd a b = 2) :
    2 ∣ b := by
  subst a
  have hd : Nat.gcd 2 b ∣ b := Nat.gcd_dvd_right 2 b
  rw [hab] at hd
  exact hd

/--
After a=q=2, the condition D_bc=1 is exactly gcd(b,c)=1.
-/
theorem bc_coprime_of_Dbc_one
    (a b c q : ℕ)
    (ha : a = 2)
    (hq : q = 2)
    (hDbc : a * Nat.gcd b c / q = 1) :
    Nat.gcd b c = 1 := by
  subst a
  subst q
  have hcancel :
      2 * Nat.gcd b c / 2 = Nat.gcd b c := by
    omega
  rw [hcancel] at hDbc
  exact hDbc

end FractionalTriangles.Section4.Lemma49FFFTwoActive
