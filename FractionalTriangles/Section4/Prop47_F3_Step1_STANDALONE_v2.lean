import Mathlib

namespace FractionalTriangles
namespace Section4

/-!
# Proposition 4.7 — f3 case, first completion step

Self-contained version.

It proves:
1. the weighted-homogeneity common-degree relations for f₃;
2. the full divisibility contradiction in Case (II).

No stack-geometric statement is asserted here.
-/

/--
For

  f₃ = x^a y + z^c y + y^b + ε x^m z^n,

weighted homogeneity of the first three monomials gives

  aA + B = h,
  cC + B = h,
  bB     = h.

Putting e=b-1, derive

  aA=eB,
  cC=eB,
  h=eB+B.
-/
theorem f3_common_degree_from_weighted_homogeneity
    (a b c A B C h : ℕ)
    (hb : 2 ≤ b)
    (hxy : a * A + B = h)
    (hzy : c * C + B = h)
    (hyb : b * B = h) :
    a * A = (b - 1) * B ∧
    c * C = (b - 1) * B ∧
    h = (b - 1) * B + B := by
  have hbdecomp : b = (b - 1) + 1 := by
    omega
  have hbprod : b * B = (b - 1) * B + B := by
    rw [hbdecomp, Nat.add_mul]
    simp
  constructor
  · have hEq : a * A + B = b * B := hxy.trans hyb.symm
    rw [hbprod] at hEq
    exact Nat.add_right_cancel hEq
  constructor
  · have hEq : c * C + B = b * B := hzy.trans hyb.symm
    rw [hbprod] at hEq
    exact Nat.add_right_cancel hEq
  · calc
      h = b * B := hyb.symm
      _ = (b - 1) * B + B := hbprod

/--
If C>1, C|e, and gcd(B,C)=1, then C does not divide (e+1)B.
-/
theorem f3_caseII_h_not_divisible
    (B C e : ℕ)
    (hC : 1 < C)
    (hCe : C ∣ e)
    (hBC : Nat.Coprime B C) :
    ¬ C ∣ (e + 1) * B := by
  intro hdiv
  have hCB : Nat.Coprime C B := hBC.symm
  have hC_e1 : C ∣ e + 1 := by
    exact (hCB.dvd_mul_right).mp hdiv
  have hC1 : C ∣ 1 := by
    have hsub : C ∣ (e + 1) - e := Nat.dvd_sub hC_e1 hCe
    simpa using hsub
  have hCeq1 : C = 1 := Nat.eq_one_of_dvd_one hC1
  omega

/--
Full arithmetic contradiction for Proposition 4.7, f₃ Case (II).

Paper assumptions:
  A=eU,
  C|e,
  gcd(B,C)=1,
  C>1,
  h=(e+1)B,

and the link homogeneity
  mA+nC=h.

Then C|A, hence C|h, but C∤h.
-/
theorem f3_caseII_full_divisibility_contradiction
    (A B C e U h m n : ℕ)
    (hC : 1 < C)
    (hA : A = e * U)
    (hCe : C ∣ e)
    (hBC : Nat.Coprime B C)
    (hh : h = (e + 1) * B)
    (hlink : m * A + n * C = h) :
    False := by
  have hCA : C ∣ A := by
    rw [hA]
    exact dvd_mul_of_dvd_left hCe U
  have hCmA : C ∣ m * A := by
    exact dvd_mul_of_dvd_right hCA m
  have hCnC : C ∣ n * C := by
    exact dvd_mul_left C n
  have hCh : C ∣ h := by
    rw [← hlink]
    exact Nat.dvd_add hCmA hCnC
  have hnot : ¬ C ∣ (e + 1) * B :=
    f3_caseII_h_not_divisible B C e hC hCe hBC
  apply hnot
  rw [← hh]
  exact hCh

end Section4
end FractionalTriangles
