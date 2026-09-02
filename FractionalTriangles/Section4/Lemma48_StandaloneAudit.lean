import Mathlib

namespace FractionalTriangles.Section4.Lemma48StandaloneAudit

/-!
Standalone arithmetic audit for Lemma 4.8.

This file imports only Mathlib.  It is intentionally independent of the
older Section 2/3 import chain.

Lean-checked here:
  (1) raw adjugate weights / weighted homogeneity for all five atomic types;
  (2) every raw and primitive open-line gcd calculation appearing in Table 2;
  (3) the gcd reductions controlling the binomial orbit counts;
  (4) the q = 1 primitivity collapses;
  (5) the five signatures in (4.13), derived from the Table-2 arithmetic.

NOT claimed as Lean-checked here:
  * geometric exhaustiveness of the coordinate strata;
  * "vertex stabilizer = primitive coordinate weight";
  * "a binomial with gcd d gives exactly d quotient points";
  * distinctness of the d roots over C;
  * absence of further dense-torus stacky points.

Those are the geometric inputs of Lemma 4.5.
-/

section RawWeights

/-- FFF: x^a + y^b + z^c. -/
theorem fff_raw_homogeneity (a b c : ℤ) :
    a * (b * c) = a * b * c ∧
    b * (a * c) = a * b * c ∧
    c * (a * b) = a * b * c := by
  constructor
  · ring
  constructor <;> ring

/-- C2F representative used in Lemma 4.8:
    x^a y + y^b + z^c. -/
theorem c2f_raw_homogeneity (a b c : ℤ) :
    a * (c * (b - 1)) + a * c = a * b * c ∧
    b * (a * c) = a * b * c ∧
    c * (a * b) = a * b * c := by
  constructor
  · ring
  constructor <;> ring

/-- L2F representative:
    x^a y + x y^b + z^c. -/
theorem l2f_raw_homogeneity (a b c : ℤ) :
    a * (c * (b - 1)) + c * (a - 1) = c * (a * b - 1) ∧
    b * (c * (a - 1)) + c * (b - 1) = c * (a * b - 1) ∧
    c * (a * b - 1) = c * (a * b - 1) := by
  constructor
  · ring
  constructor
  · ring
  · rfl

/-- C3 representative:
    x^a y + y^b z + z^c. -/
theorem c3_raw_homogeneity (a b c : ℤ) :
    a * (c * (b - 1) + 1) + a * (c - 1) = a * b * c ∧
    b * (a * (c - 1)) + a * b = a * b * c ∧
    c * (a * b) = a * b * c := by
  constructor
  · ring
  constructor <;> ring

/-- L3 representative:
    x^a y + y^b z + z^c x. -/
theorem l3_raw_homogeneity (a b c : ℤ) :
    a * (c * (b - 1) + 1) + (a * (c - 1) + 1) = a * b * c + 1 ∧
    b * (a * (c - 1) + 1) + (b * (a - 1) + 1) = a * b * c + 1 ∧
    c * (b * (a - 1) + 1) + (c * (b - 1) + 1) = a * b * c + 1 := by
  constructor
  · ring
  constructor <;> ring

end RawWeights


section RawLineGcds

/-- FFF, xy-line: raw stabilizer gcd = c gcd(a,b). -/
theorem fff_xy_raw_gcd (a b c : ℕ) :
    Nat.gcd (b * c) (a * c) = c * Nat.gcd a b := by
  simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.gcd_mul_left c b a)

/-- FFF, xz-line: raw stabilizer gcd = b gcd(a,c). -/
theorem fff_xz_raw_gcd (a b c : ℕ) :
    Nat.gcd (b * c) (a * b) = b * Nat.gcd a c := by
  simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.gcd_mul_left b c a)

/-- FFF, yz-line: raw stabilizer gcd = a gcd(b,c). -/
theorem fff_yz_raw_gcd (a b c : ℕ) :
    Nat.gcd (a * c) (a * b) = a * Nat.gcd b c := by
  simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.gcd_mul_right c a b)

/-- C2F, xy-line: raw stabilizer gcd = c r, r=gcd(a,b-1). -/
theorem c2f_xy_raw_gcd (a b c : ℕ) :
    Nat.gcd (c * (b - 1)) (a * c) =
      c * Nat.gcd a (b - 1) := by
  simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.gcd_mul_left c (b - 1) a)

/-- C2F, yz-line: raw stabilizer gcd = a s, s=gcd(b,c). -/
theorem c2f_yz_raw_gcd (a b c : ℕ) :
    Nat.gcd (a * c) (a * b) =
      a * Nat.gcd b c := by
  simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.gcd_mul_right c a b)

/-- L2F, xy-line: raw stabilizer gcd = c d, d=gcd(a-1,b-1). -/
theorem l2f_xy_raw_gcd (a b c : ℕ) :
    Nat.gcd (c * (b - 1)) (c * (a - 1)) =
      c * Nat.gcd (a - 1) (b - 1) := by
  simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.gcd_mul_right (b - 1) c (a - 1))

/-- C3, yz-line: raw stabilizer gcd = a d, d=gcd(b,c-1). -/
theorem c3_yz_raw_gcd (a b c : ℕ) :
    Nat.gcd (a * (c - 1)) (a * b) =
      a * Nat.gcd b (c - 1) := by
  simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.gcd_mul_right (c - 1) a b)

end RawLineGcds


section PrimitiveLineOrders

/-- Dividing two raw coordinate weights by a common divisor q divides
    their gcd by q. -/
theorem gcd_after_common_division
    {A B q : ℕ} (hqA : q ∣ A) (hqB : q ∣ B) :
    Nat.gcd (A / q) (B / q) = Nat.gcd A B / q := by
  exact Nat.gcd_div hqA hqB

theorem fff_xy_primitive_order
    (a b c q : ℕ) (hqA : q ∣ b * c) (hqB : q ∣ a * c) :
    Nat.gcd ((b * c) / q) ((a * c) / q) =
      (c * Nat.gcd a b) / q := by
  calc
    Nat.gcd ((b * c) / q) ((a * c) / q)
        = Nat.gcd (b * c) (a * c) / q :=
          gcd_after_common_division hqA hqB
    _ = (c * Nat.gcd a b) / q := by rw [fff_xy_raw_gcd]

theorem fff_xz_primitive_order
    (a b c q : ℕ) (hqA : q ∣ b * c) (hqC : q ∣ a * b) :
    Nat.gcd ((b * c) / q) ((a * b) / q) =
      (b * Nat.gcd a c) / q := by
  calc
    Nat.gcd ((b * c) / q) ((a * b) / q)
        = Nat.gcd (b * c) (a * b) / q :=
          gcd_after_common_division hqA hqC
    _ = (b * Nat.gcd a c) / q := by rw [fff_xz_raw_gcd]

theorem fff_yz_primitive_order
    (a b c q : ℕ) (hqB : q ∣ a * c) (hqC : q ∣ a * b) :
    Nat.gcd ((a * c) / q) ((a * b) / q) =
      (a * Nat.gcd b c) / q := by
  calc
    Nat.gcd ((a * c) / q) ((a * b) / q)
        = Nat.gcd (a * c) (a * b) / q :=
          gcd_after_common_division hqB hqC
    _ = (a * Nat.gcd b c) / q := by rw [fff_yz_raw_gcd]

theorem c2f_xy_primitive_order
    (a b c q : ℕ)
    (hqA : q ∣ c * (b - 1)) (hqB : q ∣ a * c) :
    Nat.gcd ((c * (b - 1)) / q) ((a * c) / q) =
      (c * Nat.gcd a (b - 1)) / q := by
  calc
    Nat.gcd ((c * (b - 1)) / q) ((a * c) / q)
        = Nat.gcd (c * (b - 1)) (a * c) / q :=
          gcd_after_common_division hqA hqB
    _ = (c * Nat.gcd a (b - 1)) / q := by rw [c2f_xy_raw_gcd]

theorem c2f_yz_primitive_order
    (a b c q : ℕ)
    (hqB : q ∣ a * c) (hqC : q ∣ a * b) :
    Nat.gcd ((a * c) / q) ((a * b) / q) =
      (a * Nat.gcd b c) / q := by
  calc
    Nat.gcd ((a * c) / q) ((a * b) / q)
        = Nat.gcd (a * c) (a * b) / q :=
          gcd_after_common_division hqB hqC
    _ = (a * Nat.gcd b c) / q := by rw [c2f_yz_raw_gcd]

theorem l2f_xy_primitive_order
    (a b c q : ℕ)
    (hqA : q ∣ c * (b - 1)) (hqB : q ∣ c * (a - 1)) :
    Nat.gcd ((c * (b - 1)) / q) ((c * (a - 1)) / q) =
      (c * Nat.gcd (a - 1) (b - 1)) / q := by
  calc
    Nat.gcd ((c * (b - 1)) / q) ((c * (a - 1)) / q)
        = Nat.gcd (c * (b - 1)) (c * (a - 1)) / q :=
          gcd_after_common_division hqA hqB
    _ = (c * Nat.gcd (a - 1) (b - 1)) / q := by
      rw [l2f_xy_raw_gcd]

theorem c3_yz_primitive_order
    (a b c q : ℕ)
    (hqB : q ∣ a * (c - 1)) (hqC : q ∣ a * b) :
    Nat.gcd ((a * (c - 1)) / q) ((a * b) / q) =
      (a * Nat.gcd b (c - 1)) / q := by
  calc
    Nat.gcd ((a * (c - 1)) / q) ((a * b) / q)
        = Nat.gcd (a * (c - 1)) (a * b) / q :=
          gcd_after_common_division hqB hqC
    _ = (a * Nat.gcd b (c - 1)) / q := by rw [c3_yz_raw_gcd]

end PrimitiveLineOrders


section BinomialExponentAudit

/-- If d=gcd(m,n), then m=d(m/d), n=d(n/d), and the reduced pair
    is coprime.  This is the arithmetic behind the number d in L_ij(d,D). -/
theorem binomial_gcd_reduction
    (m n : ℕ) (hm : 0 < m) :
    let d := Nat.gcd m n
    m = d * (m / d) ∧
    n = d * (n / d) ∧
    Nat.gcd (m / d) (n / d) = 1 := by
  dsimp
  have hdpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  constructor
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)).symm
  constructor
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)).symm
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_left hm

/-- FFF xy: exponents (a,b), d_ab=gcd(a,b). -/
theorem fff_xy_exponent_reduction
    (a b : ℕ) (ha : 2 ≤ a) :
    let d := Nat.gcd a b
    a = d * (a / d) ∧
    b = d * (b / d) ∧
    Nat.gcd (a / d) (b / d) = 1 := by
  exact binomial_gcd_reduction a b (by omega)

/-- FFF xz: exponents (a,c), d_ac=gcd(a,c). -/
theorem fff_xz_exponent_reduction
    (a c : ℕ) (ha : 2 ≤ a) :
    let d := Nat.gcd a c
    a = d * (a / d) ∧
    c = d * (c / d) ∧
    Nat.gcd (a / d) (c / d) = 1 := by
  exact binomial_gcd_reduction a c (by omega)

/-- FFF yz: exponents (b,c), d_bc=gcd(b,c). -/
theorem fff_yz_exponent_reduction
    (b c : ℕ) (hb : 2 ≤ b) :
    let d := Nat.gcd b c
    b = d * (b / d) ∧
    c = d * (c / d) ∧
    Nat.gcd (b / d) (c / d) = 1 := by
  exact binomial_gcd_reduction b c (by omega)

/-- C2F xy: x^a + y^(b-1), r=gcd(a,b-1). -/
theorem c2f_xy_exponent_reduction
    (a b : ℕ) (ha : 2 ≤ a) :
    let r := Nat.gcd a (b - 1)
    a = r * (a / r) ∧
    (b - 1) = r * ((b - 1) / r) ∧
    Nat.gcd (a / r) ((b - 1) / r) = 1 := by
  exact binomial_gcd_reduction a (b - 1) (by omega)

/-- C2F yz: y^b + z^c, s=gcd(b,c). -/
theorem c2f_yz_exponent_reduction
    (b c : ℕ) (hb : 2 ≤ b) :
    let s := Nat.gcd b c
    b = s * (b / s) ∧
    c = s * (c / s) ∧
    Nat.gcd (b / s) (c / s) = 1 := by
  exact binomial_gcd_reduction b c (by omega)

/-- L2F xy: x^(a-1)+y^(b-1), d=gcd(a-1,b-1). -/
theorem l2f_xy_exponent_reduction
    (a b : ℕ) (ha : 2 ≤ a) :
    let d := Nat.gcd (a - 1) (b - 1)
    (a - 1) = d * ((a - 1) / d) ∧
    (b - 1) = d * ((b - 1) / d) ∧
    Nat.gcd ((a - 1) / d) ((b - 1) / d) = 1 := by
  exact binomial_gcd_reduction (a - 1) (b - 1) (by omega)

/-- C3 yz: y^b+z^(c-1), d=gcd(b,c-1). -/
theorem c3_yz_exponent_reduction
    (b c : ℕ) (hb : 2 ≤ b) :
    let d := Nat.gcd b (c - 1)
    b = d * (b / d) ∧
    (c - 1) = d * ((c - 1) / d) ∧
    Nat.gcd (b / d) ((c - 1) / d) = 1 := by
  exact binomial_gcd_reduction b (c - 1) (by omega)

end BinomialExponentAudit


section PrimitiveCollapse

theorem common_divisor_eq_one_of_triple_gcd_one
    {d A B C : ℕ}
    (hdA : d ∣ A) (hdB : d ∣ B) (hdC : d ∣ C)
    (hq : Nat.gcd A (Nat.gcd B C) = 1) :
    d = 1 := by
  have hdBC : d ∣ Nat.gcd B C := Nat.dvd_gcd hdB hdC
  have hdABC : d ∣ Nat.gcd A (Nat.gcd B C) :=
    Nat.dvd_gcd hdA hdBC
  simpa [hq] using hdABC

/-- FFF: q=1 forces pairwise coprimality. -/
theorem fff_pairwise_of_primitive
    (a b c : ℕ)
    (hq : Nat.gcd (b * c) (Nat.gcd (a * c) (a * b)) = 1) :
    Nat.gcd a b = 1 ∧ Nat.gcd a c = 1 ∧ Nat.gcd b c = 1 := by
  constructor
  ·
    apply common_divisor_eq_one_of_triple_gcd_one
      (d := Nat.gcd a b)
      (A := b * c) (B := a * c) (C := a * b)
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) c
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) c
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) b
    · exact hq
  constructor
  ·
    apply common_divisor_eq_one_of_triple_gcd_one
      (d := Nat.gcd a c)
      (A := b * c) (B := a * c) (C := a * b)
    · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right a c) b
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a c) c
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a c) b
    · exact hq
  ·
    apply common_divisor_eq_one_of_triple_gcd_one
      (d := Nat.gcd b c)
      (A := b * c) (B := a * c) (C := a * b)
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left b c) c
    · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right b c) a
    · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left b c) a
    · exact hq

/-- FFF converse: pairwise coprimality implies q=1. -/
theorem fff_primitive_of_pairwise
    (a b c : ℕ)
    (hab : Nat.gcd a b = 1)
    (hac : Nat.gcd a c = 1)
    (hbc : Nat.gcd b c = 1) :
    Nat.gcd (b * c) (Nat.gcd (a * c) (a * b)) = 1 := by
  have hba : Nat.Coprime b a := by
    simpa [Nat.Coprime, Nat.gcd_comm] using hab
  have hca : Nat.Coprime c a := by
    simpa [Nat.Coprime, Nat.gcd_comm] using hac
  have hprod : Nat.Coprime (b * c) a := hba.mul_left hca
  calc
    Nat.gcd (b * c) (Nat.gcd (a * c) (a * b))
        = Nat.gcd (b * c) (a * Nat.gcd b c) := by
          rw [fff_yz_raw_gcd]
    _ = Nat.gcd (b * c) a := by simp [hbc]
    _ = 1 := hprod

theorem fff_primitive_iff_pairwise
    (a b c : ℕ) :
    Nat.gcd (b * c) (Nat.gcd (a * c) (a * b)) = 1 ↔
      Nat.gcd a b = 1 ∧ Nat.gcd a c = 1 ∧ Nat.gcd b c = 1 := by
  constructor
  · exact fff_pairwise_of_primitive a b c
  · intro h
    exact fff_primitive_of_pairwise a b c h.1 h.2.1 h.2.2

/-- C2F: r=gcd(a,b-1) divides all raw weights. -/
theorem c2f_r_divides_raw_weights
    (a b c : ℕ) :
    let r := Nat.gcd a (b - 1)
    r ∣ c * (b - 1) ∧ r ∣ a * c ∧ r ∣ a * b := by
  dsimp
  constructor
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right a (b - 1)) c
  constructor
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a (b - 1)) c
  · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a (b - 1)) b

/-- C2F: s=gcd(b,c) divides all raw weights. -/
theorem c2f_s_divides_raw_weights
    (a b c : ℕ) :
    let s := Nat.gcd b c
    s ∣ c * (b - 1) ∧ s ∣ a * c ∧ s ∣ a * b := by
  dsimp
  constructor
  · simpa [Nat.mul_comm] using
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right b c) (b - 1))
  constructor
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right b c) a
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left b c) a

theorem c2f_r_s_eq_one_of_primitive
    (a b c : ℕ)
    (hq :
      Nat.gcd (c * (b - 1)) (Nat.gcd (a * c) (a * b)) = 1) :
    Nat.gcd a (b - 1) = 1 ∧ Nat.gcd b c = 1 := by
  constructor
  ·
    rcases c2f_r_divides_raw_weights a b c with ⟨h1, h2, h3⟩
    exact common_divisor_eq_one_of_triple_gcd_one h1 h2 h3 hq
  ·
    rcases c2f_s_divides_raw_weights a b c with ⟨h1, h2, h3⟩
    exact common_divisor_eq_one_of_triple_gcd_one h1 h2 h3 hq

/-- L2F identity used to prove d | (ab-1). -/
theorem l2f_ab_sub_one_identity
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b - 1 = (a - 1) * b + (b - 1) := by
  have ha' : a = (a - 1) + 1 := by omega
  calc
    a * b - 1 = (((a - 1) + 1) * b) - 1 := by rw [← ha']
    _ = ((a - 1) * b + b) - 1 := by simp [Nat.add_mul]
    _ = (a - 1) * b + (b - 1) := by
      exact Nat.add_sub_assoc (by omega) ((a - 1) * b)

theorem l2f_d_divides_raw_weights
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    let d := Nat.gcd (a - 1) (b - 1)
    d ∣ c * (b - 1) ∧
    d ∣ c * (a - 1) ∧
    d ∣ (a * b - 1) := by
  dsimp
  let d := Nat.gcd (a - 1) (b - 1)
  have hdA : d ∣ a - 1 := Nat.gcd_dvd_left (a - 1) (b - 1)
  have hdB : d ∣ b - 1 := Nat.gcd_dvd_right (a - 1) (b - 1)
  constructor
  · exact dvd_mul_of_dvd_right hdB c
  constructor
  · exact dvd_mul_of_dvd_right hdA c
  ·
    rw [l2f_ab_sub_one_identity a b (by omega) (by omega)]
    exact dvd_add
      (dvd_mul_of_dvd_left hdA b)
      hdB

theorem l2f_d_eq_one_of_primitive
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hq :
      Nat.gcd (c * (b - 1))
        (Nat.gcd (c * (a - 1)) (a * b - 1)) = 1) :
    Nat.gcd (a - 1) (b - 1) = 1 := by
  rcases l2f_d_divides_raw_weights a b c ha hb with ⟨h1, h2, h3⟩
  exact common_divisor_eq_one_of_triple_gcd_one h1 h2 h3 hq

/-- C3 identity used to prove d | [c(b-1)+1]. -/
theorem c3_vertex_identity
    (b c : ℕ) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    c * (b - 1) + 1 = b + (b - 1) * (c - 1) := by
  have hb' : b = (b - 1) + 1 := by omega
  have hc' : c = (c - 1) + 1 := by omega
  rw [hb', hc']
  simp
  ring

theorem c3_d_divides_raw_weights
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    let d := Nat.gcd b (c - 1)
    d ∣ (c * (b - 1) + 1) ∧
    d ∣ a * (c - 1) ∧
    d ∣ a * b := by
  dsimp
  let d := Nat.gcd b (c - 1)
  have hdB : d ∣ b := Nat.gcd_dvd_left b (c - 1)
  have hdC : d ∣ c - 1 := Nat.gcd_dvd_right b (c - 1)
  constructor
  ·
    rw [c3_vertex_identity b c (by omega) (by omega)]
    exact dvd_add hdB (dvd_mul_of_dvd_right hdC (b - 1))
  constructor
  · exact dvd_mul_of_dvd_right hdC a
  · exact dvd_mul_of_dvd_right hdB a

theorem c3_d_eq_one_of_primitive
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hq :
      Nat.gcd (c * (b - 1) + 1)
        (Nat.gcd (a * (c - 1)) (a * b)) = 1) :
    Nat.gcd b (c - 1) = 1 := by
  rcases c3_d_divides_raw_weights a b c hb hc with ⟨h1, h2, h3⟩
  exact common_divisor_eq_one_of_triple_gcd_one h1 h2 h3 hq

end PrimitiveCollapse


section Equation413

/-- FFF: the three Table-2 line orders, put in the paper's signature order,
    collapse to (a,b,c). -/
theorem fff_signature_413
    (a b c : ℕ)
    (hq : Nat.gcd (b * c) (Nat.gcd (a * c) (a * b)) = 1) :
    (a * Nat.gcd b c,
      b * Nat.gcd a c,
      c * Nat.gcd a b) = (a, b, c) := by
  rcases fff_pairwise_of_primitive a b c hq with ⟨hab, hac, hbc⟩
  simp [hab, hac, hbc]

/-- C2F: Table 2 gives vertex order c(b-1), xy order c r,
    yz order a s.  q=1 forces r=s=1, yielding (4.13). -/
theorem c2f_signature_413
    (a b c : ℕ)
    (hq :
      Nat.gcd (c * (b - 1)) (Nat.gcd (a * c) (a * b)) = 1) :
    (a * Nat.gcd b c,
      c * (b - 1),
      c * Nat.gcd a (b - 1)) =
      (a, c * (b - 1), c) := by
  rcases c2f_r_s_eq_one_of_primitive a b c hq with ⟨hr, hs⟩
  simp [hr, hs]

/-- L2F: two vertex orders plus the xy-line order give (4.13). -/
theorem l2f_signature_413
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hq :
      Nat.gcd (c * (b - 1))
        (Nat.gcd (c * (a - 1)) (a * b - 1)) = 1) :
    (c * (a - 1),
      c * (b - 1),
      c * Nat.gcd (a - 1) (b - 1)) =
      (c * (a - 1), c * (b - 1), c) := by
  have hd := l2f_d_eq_one_of_primitive a b c ha hb hq
  simp [hd]

/-- C3: yz-line order a d plus the two vertex orders give (4.13). -/
theorem c3_signature_413
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hq :
      Nat.gcd (c * (b - 1) + 1)
        (Nat.gcd (a * (c - 1)) (a * b)) = 1) :
    (a * Nat.gcd b (c - 1),
      c * (b - 1) + 1,
      a * (c - 1)) =
      (a, c * (b - 1) + 1, a * (c - 1)) := by
  have hd := c3_d_eq_one_of_primitive a b c hb hc hq
  simp [hd]

/-- L3 has no binomial open-line contribution.  When q=1 the three
    primitive vertex weights are exactly the three entries in (4.13),
    up to the cyclic order used in the paper. -/
theorem l3_signature_413
    (a b c q : ℕ) (hq : q = 1) :
    ((b * (a - 1) + 1) / q,
      (c * (b - 1) + 1) / q,
      (a * (c - 1) + 1) / q) =
      (b * (a - 1) + 1,
       c * (b - 1) + 1,
       a * (c - 1) + 1) := by
  simp [hq]

end Equation413

end FractionalTriangles.Section4.Lemma48StandaloneAudit
