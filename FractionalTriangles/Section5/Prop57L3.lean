import Mathlib
import FractionalTriangles.Section5.Prop57Necessity

namespace FractionalTriangles
namespace Section5

/-!
# Proposition 5.7 — L3 final gcd reduction (paper pp. 21–22)

We isolate the exact divisibility argument behind
  gcd(w1,w2,w3) = gcd(m-1,w1)
for
  m=tAB,
  w1=B(t+1)+1,
  w2=t(A+1)+1,
  w3=A(B+1)+1.

No `sorry`, no axioms.
-/

/-- Any common divisor of w1,w2,w3 also divides m-1. -/
theorem l3_common_divisor_dvd_mminus1
    (A B t d : ℕ)
    (hd1 : d ∣ l3w1 B t)
    (hd3 : d ∣ l3w3 A B) :
    d ∣ l3m A B t - 1 := by
  have hA : d ∣ A * l3w1 B t := dvd_mul_of_dvd_right hd1 A
  rw [l3_identity_1 A B t] at hA
  exact Nat.dvd_sub' hA hd3

/--
If d divides m-1 and w1, and d is coprime to B, then d divides w2,
using B*w2=(m-1)+w1.
-/
theorem l3_dvd_w2_of_dvd_m_w1
    (A B t d : ℕ)
    (hdm : d ∣ l3m A B t - 1)
    (hd1 : d ∣ l3w1 B t)
    (hcop : Nat.Coprime d B) :
    d ∣ l3w2 A t := by
  have hsum : d ∣ (l3m A B t - 1) + l3w1 B t := dvd_add hdm hd1
  rw [← l3_identity_2 A B t] at hsum
  exact hcop.dvd_of_dvd_mul_right hsum

/--
If d divides m-1 and w2, and d is coprime to t, then d divides w3,
using t*w3=(m-1)+w2.
-/
theorem l3_dvd_w3_of_dvd_m_w2
    (A B t d : ℕ)
    (hdm : d ∣ l3m A B t - 1)
    (hd2 : d ∣ l3w2 A t)
    (hcop : Nat.Coprime d t) :
    d ∣ l3w3 A B := by
  have hsum : d ∣ (l3m A B t - 1) + l3w2 A t := dvd_add hdm hd2
  rw [← l3_identity_3 A B t] at hsum
  exact hcop.dvd_of_dvd_mul_right hsum

/--
A divisor of m-1 is automatically coprime to any divisor of m, because
gcd(m,m-1)=1.
-/
theorem l3_divisor_coprime_factor
    (A B t d e : ℕ)
    (hd : d ∣ l3m A B t - 1)
    (he : e ∣ l3m A B t) :
    Nat.Coprime d e := by
  apply Nat.Coprime.of_dvd
    (l3_m_coprime_m_minus_one A B t).symm hd he

/--
Thus a divisor d of m-1 and w1 divides w2 and w3 as well.
-/
theorem l3_dvd_all_of_dvd_mminus1_w1
    (A B t d : ℕ)
    (hdm : d ∣ l3m A B t - 1)
    (hd1 : d ∣ l3w1 B t) :
    d ∣ l3w2 A t ∧ d ∣ l3w3 A B := by
  have hBm : B ∣ l3m A B t := by
    refine ⟨t*A, ?_⟩
    simp [l3m]
    ring
  have htm : t ∣ l3m A B t := by
    refine ⟨A*B, ?_⟩
    simp [l3m, mul_assoc]
  have hcopB : Nat.Coprime d B :=
    l3_divisor_coprime_factor A B t d B hdm hBm
  have hd2 := l3_dvd_w2_of_dvd_m_w1 A B t d hdm hd1 hcopB
  have hcopt : Nat.Coprime d t :=
    l3_divisor_coprime_factor A B t d t hdm htm
  have hd3 := l3_dvd_w3_of_dvd_m_w2 A B t d hdm hd2 hcopt
  exact ⟨hd2, hd3⟩

/--
The paper's final L3 gcd identity.
-/
theorem l3_final_gcd_identity
    (A B t : ℕ) :
    Nat.gcd (l3w1 B t) (Nat.gcd (l3w2 A t) (l3w3 A B))
      =
    Nat.gcd (l3m A B t - 1) (l3w1 B t) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact l3_common_divisor_dvd_mminus1 A B t
        (Nat.gcd_dvd_left _ _)
        (dvd_trans (Nat.gcd_dvd_right _ _)
          (Nat.gcd_dvd_right _ _))
    · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_right _ _
    ·
      have hdm := Nat.gcd_dvd_left (l3m A B t - 1) (l3w1 B t)
      have hd1 := Nat.gcd_dvd_right (l3m A B t - 1) (l3w1 B t)
      rcases l3_dvd_all_of_dvd_mminus1_w1 A B t
        (Nat.gcd (l3m A B t - 1) (l3w1 B t)) hdm hd1 with ⟨hd2,hd3⟩
      exact Nat.dvd_gcd hd2 hd3

end Section5

end FractionalTriangles
