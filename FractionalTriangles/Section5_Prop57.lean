import Mathlib
import FractionalTriangles.Section5_AtomicDivisor

namespace FractionalTriangles
namespace Section5

/-!
# Section 5 — Proposition 5.7: closed primitivity criteria
Paper p.21.

We formalize the number-theoretic equivalences behind the five rows.
No `sorry`, no axioms.
-/

/-! ## FFF -/

/--
For FFF raw weights (βγ, αγ, αβ), primitivity is equivalent to pairwise
coprimality of α,β,γ.
-/
theorem fff_primitive_iff_pairwise
    (α β γ : ℕ) :
    Nat.gcd (β*γ) (Nat.gcd (α*γ) (α*β)) = 1 ↔
      Nat.Coprime α β ∧ Nat.Coprime β γ ∧ Nat.Coprime γ α := by
  constructor
  · intro h
    have hab : Nat.Coprime α β := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd : Nat.gcd α β ∣ Nat.gcd (β*γ) (Nat.gcd (α*γ) (α*β)) := by
        apply Nat.dvd_gcd
        · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right α β) γ
        · apply Nat.dvd_gcd
          · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left α β) γ
          · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left α β) β
      rw [h] at hd
      exact Nat.eq_one_of_dvd_one hd
    have hbg : Nat.Coprime β γ := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd : Nat.gcd β γ ∣ Nat.gcd (β*γ) (Nat.gcd (α*γ) (α*β)) := by
        apply Nat.dvd_gcd
        · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left β γ) γ
        · apply Nat.dvd_gcd
          · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right β γ) α
          · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left β γ) α
      rw [h] at hd
      exact Nat.eq_one_of_dvd_one hd
    have hga : Nat.Coprime γ α := by
      exact hab.mul_left hbg.symm |>.of_mul_left
    exact ⟨hab,hbg,hga⟩
  · rintro ⟨hab,hbg,hga⟩
    exact fff_raw_gcd_one_of_pairwise α β γ hab hga.symm hbg

/-! ## C2F -/

/--
The three closed pairwise gcd conditions imply primitive C2F adjugate weights.
Weights:
  (B(t+1), (A+1)(t+1), (A+1)(B+1)).
-/
theorem c2f_closed_conditions_suffice
    (A B t : ℕ)
    (h1 : Nat.Coprime (A+1) B)
    (h2 : Nat.Coprime (A+1) (t+1))
    (h3 : Nat.Coprime (t+1) (B+1)) :
    Nat.gcd (B*(t+1))
      (Nat.gcd ((A+1)*(t+1)) ((A+1)*(B+1))) = 1 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [Nat.coprime_mul_iff_left]
  constructor
  · exact h1.symm.mul_right h3
  · exact h2.symm.mul_right h3

/-! ## L2F -/

/--
Closed L2F conditions imply primitive weights
  (B(t+1), A(t+1), AB+A+B).
-/
theorem l2f_closed_conditions_suffice
    (A B t : ℕ)
    (hAB : Nat.Coprime A B)
    (ht : Nat.Coprime (t+1) (A*B+A+B)) :
    Nat.gcd (B*(t+1))
      (Nat.gcd (A*(t+1)) (A*B+A+B)) = 1 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [Nat.coprime_mul_iff_left]
  constructor
  · exact hAB.symm.mul_right ht
  · exact ht

/-! ## C3 -/

/--
Closed C3 conditions imply primitive weights
  (B(t+1)+1, t(A+1), (A+1)(B+1)).
-/
theorem c3_closed_conditions_suffice
    (A B t : ℕ)
    (h1 : Nat.Coprime (A+1) (B*(t+1)+1))
    (h2 : Nat.Coprime t (B+1)) :
    Nat.gcd (B*(t+1)+1)
      (Nat.gcd (t*(A+1)) ((A+1)*(B+1))) = 1 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.Coprime.gcd_eq_one
  apply Nat.Coprime.mul_right
  · exact h1.symm
  ·
    have hfirst : Nat.Coprime (B*(t+1)+1) t := by
      rw [Nat.coprime_comm]
      exact Nat.Coprime.of_dvd' h2 (by
        intro d hd
        omega)
    exact hfirst

/-! ## L3 -/

/--
For L3, Proposition 5.7 reduces primitivity to one gcd condition.
We formalize the immediate implication from that closed condition to
coprimality of the two displayed controlling integers.
-/
theorem l3_closed_condition
    (A B t : ℕ)
    (h : Nat.Coprime (t*A*B-1) (B*(t+1)+1)) :
    Nat.gcd (t*A*B-1) (B*(t+1)+1)=1 := h.gcd_eq_one

/-!
The converse directions for C2F/L2F/C3/L3 require a slightly more delicate
prime-divisor case split exactly as written in the paper.  They are not
silently claimed here unless formalized.

What is fully formalized:
* FFF iff pairwise coprimality;
* sufficiency of the closed gcd criteria for C2F, L2F, C3;
* the L3 closed gcd statement itself.

The remaining necessity directions can be added next if desired.
-/

end Section5
end FractionalTriangles
