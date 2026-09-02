import Mathlib

/-!
# Lemma 4.9 — C3 full audit

For

  g = x^a y + y^b z + z^c,

put

  p = c(b-1)+1,
  d = gcd(b,c-1),
  D = a*d/q.

The stacky-point count is

  [p/q > 1] + [a(c-1)/q > 1] + d[D > 1] = 3.

The line stratum must be active, and the second vertex is present.

Case 1: the first vertex is also present.
Then the count is 1+1+d=3, so d=1.
Adjunction reduces to 2g=q-1; genus zero gives q=1.

Case 2: the first vertex is absent.
Then p/q=1, hence q=p, and the count forces d=2.
Adjunction gives 2g=q-2.  But d=2 implies c>=3,
and b>=2, hence p=c(b-1)+1>=4.  Thus q>=4,
contradicting genus zero.

Therefore the genus-zero C3 case has q=1.
-/

namespace FractionalTriangles.Section4.Lemma49C3

/-- With both vertices present, exactly three points force d=1. -/
theorem both_vertices_force_d_one
    (d : ℕ)
    (hcount : 1 + 1 + d = 3) :
    d = 1 := by
  omega

/-- The equation q-1=0 forces q=1. -/
theorem first_vertex_present_forces_q_one
    (q : ℕ)
    (hgenus : (q : ℚ) - 1 = 0) :
    q = 1 := by
  have hqQ : (q : ℚ) = 1 := by
    linarith
  exact_mod_cast hqQ

/--
If the first vertex is absent, the remaining vertex plus the
active line must account for exactly three points, so d=2.
-/
theorem first_vertex_absent_forces_d_two
    (d : ℕ)
    (hcount : 1 + d = 3) :
    d = 2 := by
  omega

/--
If gcd(b,c-1)=2, then c>=3.
-/
theorem c_at_least_three_of_gcd_two
    (b c : ℕ)
    (hc : 2 ≤ c)
    (hd : Nat.gcd b (c - 1) = 2) :
    3 ≤ c := by
  have hdiv0 : Nat.gcd b (c - 1) ∣ c - 1 :=
    Nat.gcd_dvd_right b (c - 1)

  have hdiv : 2 ∣ c - 1 := by
    rw [hd] at hdiv0
    exact hdiv0

  have hc1pos : 0 < c - 1 := by
    omega

  have hc1two : 2 ≤ c - 1 := by
    exact Nat.le_of_dvd hc1pos hdiv

  omega

/--
For b>=2 and c>=3,

  p = c(b-1)+1 >= 4.
-/
theorem p_at_least_four
    (b c p : ℕ)
    (hb : 2 ≤ b)
    (hc : 3 ≤ c)
    (hp : p = c * (b - 1) + 1) :
    4 ≤ p := by
  have hb1 : 1 ≤ b - 1 := by
    omega

  have hmul : c ≤ c * (b - 1) := by
    have h :=
      Nat.mul_le_mul_left c hb1
    simpa using h

  omega

/--
If p/q=1 and q divides p, then p=q.

We record the exact arithmetic form needed in the paper.
-/
theorem q_eq_p_of_div_eq_one
    (p q : ℕ)
    (hq : 0 < q)
    (hpq : p / q = 1)
    (hqp : q ∣ p) :
    q = p := by
  obtain ⟨k, hpk⟩ := hqp

  have hpq' : (q * k) / q = 1 := by
    rw [← hpk]
    exact hpq

  have hk1 : k = 1 := by
    simpa [hq] using hpq'

  have hp_eq_q : p = q := by
    rw [hpk, hk1]
    simp

  exact hp_eq_q.symm

/--
The first-vertex-absent case is incompatible with genus zero.

Here q=p>=4, while adjunction at genus zero gives q-2=0.
-/
theorem absent_case_impossible
    (b c p q : ℕ)
    (hb : 2 ≤ b)
    (hc : 3 ≤ c)
    (hp : p = c * (b - 1) + 1)
    (hqp : q = p)
    (hgenus : (q : ℚ) - 2 = 0) :
    False := by
  have hp4 : 4 ≤ p :=
    p_at_least_four b c p hb hc hp

  have hq4 : 4 ≤ q := by
    omega

  have hqQ : (q : ℚ) = 2 := by
    linarith

  have hq2 : q = 2 := by
    exact_mod_cast hqQ

  omega

/--
Combined C3 conclusion at the arithmetic case-analysis level.

If the first vertex is present, genus zero gives q=1.
If it is absent, the C3 arithmetic assumptions are contradictory.
-/
theorem c3_conclusion
    (firstVertexPresent : Bool)
    (b c p q : ℕ)
    (hb : 2 ≤ b)
    (hc : 3 ≤ c)
    (hp : p = c * (b - 1) + 1)
    (hpresent :
      firstVertexPresent = true →
      (q : ℚ) - 1 = 0)
    (habsent_q :
      firstVertexPresent = false →
      q = p)
    (habsent_genus :
      firstVertexPresent = false →
      (q : ℚ) - 2 = 0) :
    q = 1 := by
  cases hfv : firstVertexPresent with
  | false =>
      exfalso
      exact absent_case_impossible
        b c p q hb hc hp
        (habsent_q hfv)
        (habsent_genus hfv)
  | true =>
      exact first_vertex_present_forces_q_one q (hpresent hfv)

end FractionalTriangles.Section4.Lemma49C3
