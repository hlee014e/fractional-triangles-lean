import Mathlib
import FractionalTriangles.Section5.Prop57L3

namespace FractionalTriangles
namespace Section6


/-!
# Section 6 — Corollary 6.1 arithmetic audit
Paper p.22.

The paper gives two explicit L3 families covering 6 ∤ δ.
We verify the gcd/primitivity arithmetic of those two families.
-/

/-- Case 3 ∤ δ: gcd(δ+3,3)=1. -/
theorem cor61_case_not_three
    (δ : ℕ)
    (h : ¬ 3 ∣ δ) :
    Nat.Coprime (δ+3) 3 := by
  rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
  have hmod : δ % 3 ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using h
  omega

/--
For weights (δ+3,2δ+3,3), if 3∤δ then the three weights are primitive.
-/
theorem cor61_weights_case1_primitive
    (δ : ℕ)
    (h : ¬ 3 ∣ δ) :
    Nat.gcd (δ+3) (Nat.gcd (2*δ+3) 3) = 1 := by
  have hc : Nat.Coprime (δ+3) 3 := cor61_case_not_three δ h
  have h2 : Nat.Coprime (2*δ+3) 3 := by
    rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
    have hmod : δ % 3 ≠ 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero] using h
    omega
  rw [Nat.coprime_iff_gcd_eq_one]
  exact hc.mul_right h2

/--
If δ≡3 mod 6, then δ+2 and δ+4 are odd consecutive odd numbers differing by 2,
hence coprime.
-/
theorem cor61_adjacent_odds_coprime
    (δ : ℕ)
    (h : δ % 6 = 3) :
    Nat.Coprime (δ+2) (δ+4) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hodd1 : (δ+2) % 2 = 1 := by omega
  have hodd2 : (δ+4) % 2 = 1 := by omega
  have hd : Nat.gcd (δ+2) (δ+4) ∣ 2 := by
    have h1 := Nat.gcd_dvd_left (δ+2) (δ+4)
    have h2 := Nat.gcd_dvd_right (δ+2) (δ+4)
    omega
  rcases Nat.dvd_prime (by decide : Nat.Prime 2) |>.mp hd with hEq | hEq
  · exact hEq
  · have htwo : 2 ∣ δ+2 := by simpa [hEq]
    exact False.elim (by
      have : (δ+2) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp htwo
      omega)

/--
Hence the second family weights (δ+4,δ+2,4) are primitive.
-/
theorem cor61_weights_case2_primitive
    (δ : ℕ)
    (h : δ % 6 = 3) :
    Nat.gcd (δ+4) (Nat.gcd (δ+2) 4) = 1 := by
  have hab : Nat.Coprime (δ+4) (δ+2) :=
    (cor61_adjacent_odds_coprime δ h).symm
  have ha4 : Nat.Coprime (δ+4) 4 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hodd : (δ+4)%2=1 := by omega
    have hd := Nat.gcd_dvd_right (δ+4) 4
    interval_cases Nat.gcd (δ+4) 4 <;> simp_all
  exact fff_raw_gcd_one_of_pairwise (δ+4) (δ+2) 4 hab ha4
    (by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hodd : (δ+2)%2=1 := by omega
      have hd := Nat.gcd_dvd_right (δ+2) 4
      interval_cases Nat.gcd (δ+2) 4 <;> simp_all)

end Section6

end FractionalTriangles
