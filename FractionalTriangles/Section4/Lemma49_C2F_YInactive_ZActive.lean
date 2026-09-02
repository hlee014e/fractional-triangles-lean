import Mathlib

/-!
# Lemma 4.9 — C2F, X=1, Y=0, Z=1

For

  g = x^a y + y^b + z^c,

put

  r = gcd(a,b-1),
  s = gcd(b,c),
  U = c*r/q.

The three-stacky-point count gives

  1 + s = 3,

hence s=2.

Equation (4.18) at genus zero becomes

  q * (1 - 1/c) - 1 = 0,

so c=q=2.

Since Y=0, the positive integer U must be 1.
After c=q=2 this gives r=1.

Finally s=gcd(b,c)=2 and c=2 imply b=2k.
Thus gcd(a,2k-1)=1.

This is the arithmetic content of family (4.20).
-/

namespace FractionalTriangles.Section4.Lemma49C2FYInactiveZActive

/-- The stacky-point count forces s=2. -/
theorem count_forces_s_two
    (s : ℕ)
    (hcount : 1 + s = 3) :
    s = 2 := by
  omega

/--
The genus-zero equation forces c=q=2.
-/
theorem genus_zero_forces_c_q_two
    (c q : ℕ)
    (hc : 2 ≤ c)
    (hq : 2 ≤ q)
    (h :
      (q : ℚ) * (1 - 1 / (c : ℚ)) - 1 = 0) :
    c = 2 ∧ q = 2 := by
  have hcQ : (2 : ℚ) ≤ (c : ℚ) := by
    exact_mod_cast hc
  have hqQ : (2 : ℚ) ≤ (q : ℚ) := by
    exact_mod_cast hq
  have hc0 : (c : ℚ) ≠ 0 := by
    positivity

  field_simp [hc0] at h

  have hc_eqQ : (c : ℚ) = 2 := by
    nlinarith

  have hq_eqQ : (q : ℚ) = 2 := by
    nlinarith

  constructor
  · exact_mod_cast hc_eqQ
  · exact_mod_cast hq_eqQ

/--
After c=q=2, U=1 forces r=1.
-/
theorem r_one_of_U_one
    (c r q : ℕ)
    (hc : c = 2)
    (hq : q = 2)
    (hU : c * r / q = 1) :
    r = 1 := by
  subst c
  subst q
  have hcancel : 2 * r / 2 = r := by
    omega
  rw [hcancel] at hU
  exact hU

/--
If c=2 and gcd(b,c)=2, then b is even.
-/
theorem b_even_of_s_two
    (b c : ℕ)
    (hc : c = 2)
    (hs : Nat.gcd b c = 2) :
    2 ∣ b := by
  subst c
  have hd : Nat.gcd b 2 ∣ b :=
    Nat.gcd_dvd_left b 2
  rw [hs] at hd
  exact hd

/--
An even natural b can be written as b=2k.
-/
theorem b_is_even_form
    (b : ℕ)
    (heven : 2 ∣ b) :
    ∃ k : ℕ, b = 2 * k := by
  obtain ⟨k, hk⟩ := heven
  exact ⟨k, hk⟩

/--
Arithmetic conclusion corresponding to family (4.20).
-/
theorem family_420_arithmetic
    (a b c q : ℕ)
    (hc : c = 2)
    (hq : q = 2)
    (hr : Nat.gcd a (b - 1) = 1)
    (hs : Nat.gcd b c = 2) :
    ∃ k : ℕ,
      b = 2 * k ∧
      Nat.gcd a (2 * k - 1) = 1 := by

  have heven : 2 ∣ b :=
    b_even_of_s_two b c hc hs

  obtain ⟨k, hk⟩ :=
    b_is_even_form b heven

  use k
  constructor
  · exact hk
  · rw [← hk]
    exact hr

end FractionalTriangles.Section4.Lemma49C2FYInactiveZActive
