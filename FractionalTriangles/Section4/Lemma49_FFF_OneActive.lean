import Mathlib

/-!
# Lemma 4.9 — FFF, one active coordinate pair

In the one-active-pair case, the unique active coordinate line
contains all three nontrivial stacky points. Hence

  gcd(a,b) = 3.

Moreover gcd(a,b) divides q, so 3 divides q.

At genus zero, equation (4.15) becomes

  q * (1 - 1/a - 1/b) - 1 = 0.

For a,b >= 3 these conditions force

  a = b = q = 3.

This is the arithmetic core of equation (4.17).
-/

namespace FractionalTriangles.Section4.Lemma49FFFOneActive

theorem one_active_forces_three
    (a b q : ℕ)
    (ha : 3 ≤ a)
    (hb : 3 ≤ b)
    (hgcd : Nat.gcd a b = 3)
    (hgcd_q : Nat.gcd a b ∣ q)
    (h :
      (q : ℚ) *
          (1 - 1 / (a : ℚ) - 1 / (b : ℚ))
        - 1 = 0) :
    a = 3 ∧ b = 3 ∧ q = 3 := by

  have hdiv : 3 ∣ q := by
    rw [hgcd] at hgcd_q
    exact hgcd_q

  have hqpos : 0 < q := by
    by_contra hn
    have hq0 : q = 0 := by omega
    subst q
    norm_num at h

  have hq3 : 3 ≤ q := Nat.le_of_dvd hqpos hdiv

  have haQ : (3 : ℚ) ≤ (a : ℚ) := by
    exact_mod_cast ha
  have hbQ : (3 : ℚ) ≤ (b : ℚ) := by
    exact_mod_cast hb
  have hqQ : (3 : ℚ) ≤ (q : ℚ) := by
    exact_mod_cast hq3

  have ha0 : (a : ℚ) ≠ 0 := by
    positivity
  have hb0 : (b : ℚ) ≠ 0 := by
    positivity

  have hmain :
      (q : ℚ) *
          (1 - 1 / (a : ℚ) - 1 / (b : ℚ))
        = 1 := by
    linarith

  /-
  Clearing denominators gives

      q(ab-a-b) = ab.
  -/
  have hpoly :
      (q : ℚ) *
          ((a : ℚ) * (b : ℚ) - (a : ℚ) - (b : ℚ))
        =
      (a : ℚ) * (b : ℚ) := by
    calc
      (q : ℚ) *
          ((a : ℚ) * (b : ℚ) - (a : ℚ) - (b : ℚ))
          =
        (a : ℚ) * (b : ℚ) *
          ((q : ℚ) *
            (1 - 1 / (a : ℚ) - 1 / (b : ℚ))) := by
              field_simp [ha0, hb0]
              <;> ring
      _ = (a : ℚ) * (b : ℚ) := by
        rw [hmain]
        ring

  /-
  For a,b >= 3,

      3(ab-a-b) >= ab.

  Indeed

      3(ab-a-b) - ab
        = 2ab - 3a - 3b
        = 2(a-3)(b-3) + 3(a-3) + 3(b-3) >= 0.
  -/
  have hab_nonneg :
      0 ≤ ((a : ℚ) - 3) * ((b : ℚ) - 3) := by
    positivity

  have hthree :
      (a : ℚ) * (b : ℚ) ≤
        3 * ((a : ℚ) * (b : ℚ) - (a : ℚ) - (b : ℚ)) := by
    nlinarith [hab_nonneg]

  have hDpos :
      0 <
        (a : ℚ) * (b : ℚ) - (a : ℚ) - (b : ℚ) := by
    nlinarith [haQ, hbQ, hab_nonneg]

  /-
  Since q >= 3 and

      q(ab-a-b) = ab <= 3(ab-a-b),

  positivity of ab-a-b forces q <= 3.
  Hence q=3.
  -/
  have hq_minus :
      0 ≤ ((q : ℚ) - 3) := by
    linarith

  have hprod :
      0 ≤
        ((q : ℚ) - 3) *
          ((a : ℚ) * (b : ℚ) - (a : ℚ) - (b : ℚ)) :=
    mul_nonneg hq_minus (le_of_lt hDpos)

  have hq_eqQ : (q : ℚ) = 3 := by
    nlinarith [hpoly, hthree, hprod]

  have hq_eq : q = 3 := by
    exact_mod_cast hq_eqQ

  /-
  With q=3, equality holds in the preceding inequality:

      2ab - 3a - 3b = 0.

  For a,b >= 3 this forces a=b=3.
  -/
  have hab_eq :
      2 * (a : ℚ) * (b : ℚ)
        - 3 * (a : ℚ)
        - 3 * (b : ℚ) = 0 := by
    rw [hq_eqQ] at hpoly
    nlinarith [hpoly]

  have ha_eqQ : (a : ℚ) = 3 := by
    nlinarith [hab_eq, hab_nonneg, haQ, hbQ]

  have hb_eqQ : (b : ℚ) = 3 := by
    nlinarith [hab_eq, hab_nonneg, haQ, hbQ]

  have ha_eq : a = 3 := by
    exact_mod_cast ha_eqQ

  have hb_eq : b = 3 := by
    exact_mod_cast hb_eqQ

  exact ⟨ha_eq, hb_eq, hq_eq⟩

end FractionalTriangles.Section4.Lemma49FFFOneActive
