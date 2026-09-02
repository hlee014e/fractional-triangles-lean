import Mathlib

/-!
# Lemma 4.9 — C2F, Y = 1 and Z = 0

For

  g = x^a y + y^b + z^c,

put

  r = gcd(a,b-1),
  s = gcd(b,c),
  V = a*s/q.

In this subcase Y=1 implies X=1, while Z=0.

The three-stacky-point count therefore gives

  1 + r = 3,

hence r=2.

Equation (4.18) at genus zero becomes

  q * (1 - 1/a) - 1 = 0,

so a=q=2.

Then gcd(a,b-1)=2 implies b=2k+1, and V=1 gives gcd(b,c)=1.
This is the arithmetic content of family (4.19).
-/

namespace FractionalTriangles.Section4.Lemma49C2FYActiveZInactive

/-- The point count 1+r=3 forces r=2. -/
theorem count_forces_r_two
    (r : ℕ)
    (hcount : 1 + r = 3) :
    r = 2 := by
  omega

/--
The genus-zero equation in this C2F subcase forces a=q=2.
-/
theorem genus_zero_forces_a_q_two
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

  have ha_eqQ : (a : ℚ) = 2 := by
    nlinarith

  have hq_eqQ : (q : ℚ) = 2 := by
    nlinarith

  constructor
  · exact_mod_cast ha_eqQ
  · exact_mod_cast hq_eqQ

/--
If a=2 and gcd(a,b-1)=2, then b-1 is even.
-/
theorem b_sub_one_even
    (a b : ℕ)
    (ha : a = 2)
    (hr : Nat.gcd a (b - 1) = 2) :
    2 ∣ b - 1 := by
  subst a
  have hd :
      Nat.gcd 2 (b - 1) ∣ b - 1 :=
    Nat.gcd_dvd_right 2 (b - 1)
  rw [hr] at hd
  exact hd

/--
For b>=1, divisibility 2 | (b-1) gives b=2k+1.
-/
theorem b_is_odd_form
    (b : ℕ)
    (hb : 1 ≤ b)
    (heven : 2 ∣ b - 1) :
    ∃ k : ℕ, b = 2 * k + 1 := by
  obtain ⟨k, hk⟩ := heven
  use k
  omega

/--
A positive natural stabilizer order which is not >1 must equal 1.

This records the arithmetic meaning of an inactive stratum.
-/
theorem inactive_positive_order_eq_one
    (V : ℕ)
    (hVpos : 0 < V)
    (hVinactive : ¬ 1 < V) :
    V = 1 := by
  omega

/--
After a=q=2, V=1 implies gcd(b,c)=1.
-/
theorem gcd_bc_one_of_V_one
    (a b c q : ℕ)
    (ha : a = 2)
    (hq : q = 2)
    (hV :
      a * Nat.gcd b c / q = 1) :
    Nat.gcd b c = 1 := by
  subst a
  subst q
  have hcancel :
      2 * Nat.gcd b c / 2 = Nat.gcd b c := by
    omega
  rw [hcancel] at hV
  exact hV

/--
Combined arithmetic conclusion corresponding to family (4.19):
there is k with b=2k+1, and gcd(b,c)=1.
-/
theorem family_419_arithmetic
    (a b c q : ℕ)
    (hb : 2 ≤ b)
    (haeq : a = 2)
    (hqeq : q = 2)
    (hr : Nat.gcd a (b - 1) = 2)
    (hV :
      a * Nat.gcd b c / q = 1) :
    ∃ k : ℕ,
      b = 2 * k + 1 ∧
      Nat.gcd b c = 1 := by
  have heven : 2 ∣ b - 1 :=
    b_sub_one_even a b haeq hr

  have hb1 : 1 ≤ b := by
    omega

  obtain ⟨k, hk⟩ :=
    b_is_odd_form b hb1 heven

  have hcoprime : Nat.gcd b c = 1 :=
    gcd_bc_one_of_V_one a b c q haeq hqeq hV

  exact ⟨k, hk, hcoprime⟩

end FractionalTriangles.Section4.Lemma49C2FYActiveZInactive
