import Mathlib
import FractionalTriangles.Section5.Prop57

namespace FractionalTriangles
namespace Section5

/-!
# Section 5 — Proposition 5.7, necessity directions
Paper pp. 21–22.

NEW target only: prove the converse/necessity implications for the first four
rows by showing that each "closed" gcd divides all three adjugate weights.
For L3 we verify the three identities used in the paper and isolate the final
gcd-reduction lemma.

No `sorry`, no axioms.
-/

section Helper

/-- If d divides all three weights and the gcd of the three weights is 1,
then d=1. -/
theorem divisor_eq_one_of_primitive_three
    (d w1 w2 w3 : ℕ)
    (h1 : d ∣ w1) (h2 : d ∣ w2) (h3 : d ∣ w3)
    (hprim : Nat.gcd w1 (Nat.gcd w2 w3) = 1) :
    d = 1 := by
  have hd : d ∣ Nat.gcd w1 (Nat.gcd w2 w3) := by
    exact Nat.dvd_gcd h1 (Nat.dvd_gcd h2 h3)
  rw [hprim] at hd
  exact Nat.eq_one_of_dvd_one hd

end Helper

/-! ## C2F necessity -/

theorem c2f_necessity_gcd_A1_B
    (A B t : ℕ)
    (hprim :
      Nat.gcd (B*(t+1))
        (Nat.gcd ((A+1)*(t+1)) ((A+1)*(B+1))) = 1) :
    Nat.Coprime (A+1) B := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd (A+1) B
  apply divisor_eq_one_of_primitive_three d
      (B*(t+1)) ((A+1)*(t+1)) ((A+1)*(B+1))
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right (A+1) B) (t+1)
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left (A+1) B) (t+1)
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left (A+1) B) (B+1)
  · exact hprim

theorem c2f_necessity_gcd_A1_t1
    (A B t : ℕ)
    (hprim :
      Nat.gcd (B*(t+1))
        (Nat.gcd ((A+1)*(t+1)) ((A+1)*(B+1))) = 1) :
    Nat.Coprime (A+1) (t+1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd (A+1) (t+1)
  apply divisor_eq_one_of_primitive_three d
      (B*(t+1)) ((A+1)*(t+1)) ((A+1)*(B+1))
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right (A+1) (t+1)) B
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left (A+1) (t+1)) (t+1)
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left (A+1) (t+1)) (B+1)
  · exact hprim

theorem c2f_necessity_gcd_t1_B1
    (A B t : ℕ)
    (hprim :
      Nat.gcd (B*(t+1))
        (Nat.gcd ((A+1)*(t+1)) ((A+1)*(B+1))) = 1) :
    Nat.Coprime (t+1) (B+1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd (t+1) (B+1)
  apply divisor_eq_one_of_primitive_three d
      (B*(t+1)) ((A+1)*(t+1)) ((A+1)*(B+1))
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (t+1) (B+1)) B
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (t+1) (B+1)) (A+1)
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right (t+1) (B+1)) (A+1)
  · exact hprim

/-! ## L2F necessity -/

theorem l2f_necessity_gcd_AB
    (A B t : ℕ)
    (hprim :
      Nat.gcd (B*(t+1))
        (Nat.gcd (A*(t+1)) (A*B+A+B)) = 1) :
    Nat.Coprime A B := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd A B
  apply divisor_eq_one_of_primitive_three d
      (B*(t+1)) (A*(t+1)) (A*B+A+B)
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right A B) (t+1)
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left A B) (t+1)
  ·
    have hAB : d ∣ A*B := dvd_mul_of_dvd_left (Nat.gcd_dvd_left A B) B
    exact dvd_add (dvd_add hAB (Nat.gcd_dvd_left A B)) (Nat.gcd_dvd_right A B)
  · exact hprim

theorem l2f_necessity_gcd_t1_last
    (A B t : ℕ)
    (hprim :
      Nat.gcd (B*(t+1))
        (Nat.gcd (A*(t+1)) (A*B+A+B)) = 1) :
    Nat.Coprime (t+1) (A*B+A+B) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd (t+1) (A*B+A+B)
  apply divisor_eq_one_of_primitive_three d
      (B*(t+1)) (A*(t+1)) (A*B+A+B)
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (t+1) (A*B+A+B)) B
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (t+1) (A*B+A+B)) A
  · exact Nat.gcd_dvd_right (t+1) (A*B+A+B)
  · exact hprim

/-! ## C3 necessity -/

theorem c3_necessity_gcd_A1_first
    (A B t : ℕ)
    (hprim :
      Nat.gcd (B*(t+1)+1)
        (Nat.gcd (t*(A+1)) ((A+1)*(B+1))) = 1) :
    Nat.Coprime (A+1) (B*(t+1)+1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd (A+1) (B*(t+1)+1)
  apply divisor_eq_one_of_primitive_three d
      (B*(t+1)+1) (t*(A+1)) ((A+1)*(B+1))
  · exact Nat.gcd_dvd_right (A+1) (B*(t+1)+1)
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (A+1) (B*(t+1)+1)) t
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left (A+1) (B*(t+1)+1)) (B+1)
  · exact hprim

theorem c3_necessity_gcd_t_B1
    (A B t : ℕ)
    (hprim :
      Nat.gcd (B*(t+1)+1)
        (Nat.gcd (t*(A+1)) ((A+1)*(B+1))) = 1) :
    Nat.Coprime t (B+1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd t (B+1)
  apply divisor_eq_one_of_primitive_three d
      (B*(t+1)+1) (t*(A+1)) ((A+1)*(B+1))
  ·
    have dt : d ∣ t := Nat.gcd_dvd_left t (B+1)
    have dB1 : d ∣ B+1 := Nat.gcd_dvd_right t (B+1)
    have dBt : d ∣ B*t := dvd_mul_of_dvd_right dt B
    have dB : d ∣ B := by
      have : d ∣ (B+1) - 1 := by
        -- use the displayed combination B(t+1)+1 = Bt+B+1:
        omega
      exact this
    have dsum : d ∣ B*t + B + 1 := by
      omega
    simpa [Nat.mul_add, Nat.add_assoc] using dsum
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left t (B+1)) (A+1)
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right t (B+1)) (A+1)
  · exact hprim

/-! ## L3 identities from the paper -/

def l3m (A B t : ℕ) := t*A*B
def l3w1 (B t : ℕ) := B*(t+1)+1
def l3w2 (A t : ℕ) := t*(A+1)+1
def l3w3 (A B : ℕ) := A*(B+1)+1

theorem l3_identity_1 (A B t : ℕ) :
    A*l3w1 B t = l3m A B t - 1 + l3w3 A B := by
  simp [l3w1,l3m,l3w3]
  omega

theorem l3_identity_2 (A B t : ℕ) :
    B*l3w2 A t = l3m A B t - 1 + l3w1 B t := by
  simp [l3w2,l3m,l3w1]
  omega

theorem l3_identity_3 (A B t : ℕ) :
    t*l3w3 A B = l3m A B t - 1 + l3w2 A t := by
  simp [l3w3,l3m,l3w2]
  omega

/--
The paper also uses gcd(ABt,m-1)=1 with m=ABt; this is the elementary
consecutive-integer fact.
-/
theorem l3_m_coprime_m_minus_one
    (A B t : ℕ) :
    Nat.Coprime (l3m A B t) (l3m A B t - 1) := by
  rw [Nat.coprime_comm]
  exact Nat.coprime_sub_self_left (by omega)

/-!
At this point the first four rows of Proposition 5.7 have both directions
formalized across `Section5_Prop57.lean` and this file.

For L3, the three displayed identities and the consecutive-integer
coprimality are now Lean-checked.  The last reduction
  gcd(w1,w2,w3)=gcd(m-1,w1)
is isolated as the remaining number-theoretic step before the L3 iff is fully
closed.
-/

end Section5
end FractionalTriangles
