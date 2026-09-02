import Mathlib

/-!
# Lemma 4.9 — C2F remaining case

For

  g = x^a y + y^b + z^c,

put e=b-1 and s=gcd(b,c).

The remaining case is

  X=0, Y=0, Z=1.

The exactly-three-stacky-points condition gives s=3.

The genus-zero specialization of equation (4.18) gives

  e(c-1)=2.

Since e>=1 and c>=2, the only possibilities are

  (e,c)=(1,3) or (2,2).

Since b=e+1, either possibility gives gcd(b,c)=1,
contradicting s=3.

Thus the remaining C2F case is impossible.
-/

namespace FractionalTriangles.Section4.Lemma49C2FRemaining

/--
Positive natural solutions of e(c-1)=2 are exactly
(e,c)=(1,3) or (2,2).
-/
theorem ec_minus_one_eq_two_cases
    (e c : ℕ)
    (he : 1 ≤ e)
    (hc : 2 ≤ c)
    (h : e * (c - 1) = 2) :
    (e = 1 ∧ c = 3) ∨
    (e = 2 ∧ c = 2) := by

  have he_dvd : e ∣ 2 := by
    use c - 1
    exact h.symm

  have he_le : e ≤ 2 := by
    exact Nat.le_of_dvd (by norm_num) he_dvd

  have he_cases : e = 1 ∨ e = 2 := by
    omega

  rcases he_cases with he1 | he2

  · left
    constructor
    · exact he1
    · subst e
      norm_num at h
      omega

  · right
    constructor
    · exact he2
    · subst e
      norm_num at h
      omega

/--
If b=e+1 and e(c-1)=2, then gcd(b,c)=1.
-/
theorem gcd_eq_one_of_genus_zero
    (e b c : ℕ)
    (he : 1 ≤ e)
    (hc : 2 ≤ c)
    (hb : b = e + 1)
    (h : e * (c - 1) = 2) :
    Nat.gcd b c = 1 := by
  rcases ec_minus_one_eq_two_cases e c he hc h with hcase | hcase
  · rcases hcase with ⟨he1, hc3⟩
    subst e
    subst c
    simp at hb
    subst b
    norm_num
  · rcases hcase with ⟨he2, hc2⟩
    subst e
    subst c
    simp at hb
    subst b
    norm_num

/--
The remaining C2F case is impossible:
genus zero gives e(c-1)=2, whereas the three-point count
requires gcd(b,c)=3.
-/
theorem remaining_case_impossible
    (e b c : ℕ)
    (he : 1 ≤ e)
    (hc : 2 ≤ c)
    (hb : b = e + 1)
    (hgenus : e * (c - 1) = 2)
    (hs : Nat.gcd b c = 3) :
    False := by
  have hgcd : Nat.gcd b c = 1 :=
    gcd_eq_one_of_genus_zero e b c he hc hb hgenus
  omega

end FractionalTriangles.Section4.Lemma49C2FRemaining
