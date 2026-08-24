import Mathlib
import FractionalTriangles.Section4_GraphBranched

namespace FractionalTriangles
namespace Section4

/-!
# Section 4 — Lemma 4.8, Table 2 and signatures (4.13)
Paper p.13.

This file checks the arithmetic formulas behind the coordinate-stratum audit.
Geometric exhaustiveness still uses Lemma 4.5.

No `sorry`, no axioms.
-/

section FFF

/-- Raw FFF weights (bc,ac,ab) have gcd 1 iff a,b,c are pairwise coprime. -/
theorem fff_raw_gcd_one_of_pairwise
    (a b c : ℕ)
    (hab : Nat.Coprime a b)
    (hac : Nat.Coprime a c)
    (hbc : Nat.Coprime b c) :
    Nat.gcd (b*c) (Nat.gcd (a*c) (a*b)) = 1 := by
  rw [Nat.Coprime.gcd_eq_one]
  rw [Nat.coprime_iff_gcd_eq_one] at hab hac hbc
  rw [Nat.coprime_mul_iff_left]
  constructor
  · exact hbc
  · exact hab.symm.mul_left hac.symm

end FFF

section DivisorCollapse

/--
C2F: r=gcd(a,b-1) divides all three raw weights
(c(b-1), ac, ab).
-/
theorem c2f_r_divides_raw_weights
    (a b c : ℕ) :
    let r := Nat.gcd a (b-1)
    r ∣ c*(b-1) ∧ r ∣ a*c ∧ r ∣ a*b := by
  dsimp
  constructor
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right a (b-1)) c
  constructor
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a (b-1)) c
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a (b-1)) b

/--
C2F: s=gcd(b,c) also divides all three raw weights.
-/
theorem c2f_s_divides_raw_weights
    (a b c : ℕ) :
    let s := Nat.gcd b c
    s ∣ c*(b-1) ∧ s ∣ a*c ∧ s ∣ a*b := by
  dsimp
  constructor
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right b c) (b-1)
  constructor
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right b c) a
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left b c) a

/--
L2F: d=gcd(a-1,b-1) divides all three raw weights
(c(b-1), c(a-1), ab-1).
-/
theorem l2f_d_divides_raw_weights
    (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let d := Nat.gcd (a-1) (b-1)
    d ∣ c*(b-1) ∧ d ∣ c*(a-1) ∧ d ∣ (a*b-1) := by
  dsimp
  constructor
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right (a-1) (b-1)) c
  constructor
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (a-1) (b-1)) c
  · have h1 : Nat.gcd (a-1) (b-1) ∣ (a-1)*(b-1) := by
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left (a-1) (b-1)) (b-1)
    have h2 : Nat.gcd (a-1) (b-1) ∣ (a-1) + (b-1) := by
      exact dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    have hid : a*b - 1 = (a-1)*(b-1) + (a-1) + (b-1) := by omega
    rw [hid]
    exact dvd_add (dvd_add h1 (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)

/--
C3: d=gcd(b,c-1) divides the three raw weights
(c(b-1)+1, a(c-1), ab).
The first divisibility follows from c≡1 and b≡0 mod d.
-/
theorem c3_d_divides_raw_weights
    (a b c : ℕ) (hc : 1 ≤ c) :
    let d := Nat.gcd b (c-1)
    d ∣ (c*(b-1)+1) ∧ d ∣ a*(c-1) ∧ d ∣ a*b := by
  dsimp
  constructor
  · have db : Nat.gcd b (c-1) ∣ b := Nat.gcd_dvd_left _ _
    have dc : Nat.gcd b (c-1) ∣ c-1 := Nat.gcd_dvd_right _ _
    have hcb : Nat.gcd b (c-1) ∣ c*b - c + 1 := by
      have hcb' : Nat.gcd b (c-1) ∣ c*b := dvd_mul_of_dvd_right db c
      have hc1 : Nat.gcd b (c-1) ∣ c-1 := dc
      omega
    have hid : c*(b-1)+1 = c*b-c+1 := by omega
    simpa [hid] using hcb
  constructor
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right b (c-1)) a
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left b (c-1)) a

end DivisorCollapse

section SignatureFormulas

/--
The q=1 signatures displayed in (4.13), packaged exactly as numerical triples.
-/
def signatureFFF (a b c : ℕ) := (a,b,c)
def signatureC2F (a b c : ℕ) := (a, c*(b-1), c)
def signatureL2F (a b c : ℕ) := (c*(a-1), c*(b-1), c)
def signatureC3  (a b c : ℕ) := (a, c*(b-1)+1, a*(c-1))
def signatureL3  (a b c : ℕ) :=
  (b*(a-1)+1, c*(b-1)+1, a*(c-1)+1)

theorem signatures_413
    (a b c : ℕ) :
    signatureFFF a b c = (a,b,c) ∧
    signatureC2F a b c = (a,c*(b-1),c) ∧
    signatureL2F a b c = (c*(a-1),c*(b-1),c) ∧
    signatureC3 a b c = (a,c*(b-1)+1,a*(c-1)) ∧
    signatureL3 a b c =
      (b*(a-1)+1,c*(b-1)+1,a*(c-1)+1) := by
  rfl

/-- Under a,b,c≥2 all displayed L3 orders are nontrivial. -/
theorem l3_orders_at_least_two
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    2 ≤ b*(a-1)+1 ∧
    2 ≤ c*(b-1)+1 ∧
    2 ≤ a*(c-1)+1 := by
  omega

end SignatureFormulas

/-!
FULL Lemma 4.8 still depends on the geometric statement that Table 2 is
exhaustive: restricting each atomic polynomial to every coordinate vertex and
open coordinate line, applying Lemma 4.5, and excluding additional dense-torus
stabilizer strata.

What is Lean-checked here is the divisibility/primitivity arithmetic used in
the last paragraph of Lemma 4.8 and the exact numerical signature formulas
(4.13).
-/

end Section4
end FractionalTriangles
