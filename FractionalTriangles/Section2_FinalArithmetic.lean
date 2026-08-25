import Mathlib
import FractionalTriangles.Section2_RootCriterion
import FractionalTriangles.Section2_DegreeAndRootArithmetic

namespace FractionalTriangles

/-!
# Section 2 — final paper-level arithmetic targets

Paper basis: `fractional_triangles_v04(2).pdf`, Section 2, pp. 5–6:
equation (2.4), proof of Theorem 1.1, equations (2.5), (2.6), and Remark 2.2.

This file formalizes the arithmetic content of the two remaining steps:
1. the congruence consequence of reducing modulo `Z c`;
2. the explicit maximal-root formula (2.6), once the divisibility/congruence
   hypotheses on the integers `b_i` are supplied.

No `sorry` and no axioms are used.

The full categorical isomorphism
  L / Z c ≃ Z/p ⊕ Z/q ⊕ Z/r
is not constructed here; instead we formalize exactly the congruence consequence
that the proof uses. Thus this closes the arithmetic proof of Theorem 1.1, while
the literal quotient-isomorphism statement (2.4) remains a separate structural
formalization target.
-/

/-- If `δ*s ≡ -1 (mod p)`, then `δ` and `p` are coprime. -/
theorem coprime_of_mul_modEq_neg_one
    (δ p : ℕ) (s : ℤ)
    (h : Int.ModEq p ((δ : ℤ) * s) (-1 : ℤ)) :
    Nat.Coprime δ p := by
  rw [Int.modEq_iff_dvd] at h
  have hdvd : (p : ℤ) ∣ (δ : ℤ) * s + 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  rcases hdvd with ⟨t, ht⟩
  have hbez : (1 : ℤ) = (p : ℤ) * t - (δ : ℤ) * s := by
    linarith
  rw [Nat.coprime_iff_gcd_eq_one]
  have hgcdpos : 0 < Nat.gcd δ p := by
    by_contra hz
    have h0 : Nat.gcd δ p = 0 := Nat.eq_zero_of_not_pos hz
    have hdδ := Nat.gcd_dvd_left δ p
    have hdp := Nat.gcd_dvd_right δ p
    rw [h0] at hdδ hdp
    simp at hdδ hdp
    subst δ
    subst p
    simp at hbez
  have hgcd_dvd_delta : Nat.gcd δ p ∣ δ := Nat.gcd_dvd_left δ p
  have hgcd_dvd_p : Nat.gcd δ p ∣ p := Nat.gcd_dvd_right δ p
  rcases hgcd_dvd_delta with ⟨a, ha⟩
  rcases hgcd_dvd_p with ⟨b, hb⟩
  have hgcd_dvd_one : (Nat.gcd δ p : ℤ) ∣ 1 := by
    refine ⟨(b : ℤ) * t - (a : ℤ) * s, ?_⟩
    rw [ha, hb] at hbez
    norm_num at hbez ⊢
    linarith
  have habs : Int.natAbs (Nat.gcd δ p : ℤ) = 1 := by
    have := Int.natAbs_dvd_natAbs.mpr hgcd_dvd_one
    simpa using this
  simpa using habs

/-- Three residue congruences imply coprimality with the lcm. -/
theorem theorem11_coprime_lcm_of_residue_congruences
    (δ p q r : ℕ) (sp sq sr : ℤ)
    (hp : Int.ModEq p ((δ : ℤ) * sp) (-1 : ℤ))
    (hq : Int.ModEq q ((δ : ℤ) * sq) (-1 : ℤ))
    (hr : Int.ModEq r ((δ : ℤ) * sr) (-1 : ℤ)) :
    Nat.Coprime δ (Nat.lcm p (Nat.lcm q r)) := by
  have cp : Nat.Coprime δ p := coprime_of_mul_modEq_neg_one δ p sp hp
  have cq : Nat.Coprime δ q := coprime_of_mul_modEq_neg_one δ q sq hq
  have cr : Nat.Coprime δ r := coprime_of_mul_modEq_neg_one δ r sr hr
  rw [Nat.coprime_lcm_iff]
  constructor
  · exact cp
  · rw [Nat.coprime_lcm_iff]
    exact ⟨cq, cr⟩

/-- Integer witness behind `(b p - 1)/d` in formula (2.6). -/
theorem coefficient_witness
    (b p d : ℤ)
    (h : Int.ModEq d (b * p) 1) :
    ∃ a : ℤ, b * p - 1 = d * a := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [sub_eq_add_neg, mul_comm] using ha

/--
Literal algebra behind equation (2.6).
Given integer coefficients satisfying the displayed divisibilities,
the element
  ϖ = A c + Bx x + By y + Bz z
satisfies d ϖ = ω.
-/
theorem explicit_maximal_root_formula
    (p q r d : ℕ)
    (bx by bz A Bx By Bz : ℤ)
    (hA : 1 - bx - by - bz = (d : ℤ) * A)
    (hBx : bx * (p : ℤ) - 1 = (d : ℤ) * Bx)
    (hBy : by * (q : ℤ) - 1 = (d : ℤ) * By)
    (hBz : bz * (r : ℤ) - 1 = (d : ℤ) * Bz) :
    d •
      (A • cbar p q r +
       Bx • xbar p q r +
       By • ybar p q r +
       Bz • zbar p q r)
      = omega p q r := by
  have hpx : (p : ℤ) • xbar p q r = cbar p q r := by
    simpa using p_x_eq_c p q r
  have hqy : (q : ℤ) • ybar p q r = cbar p q r := by
    simpa using q_y_eq_c p q r
  have hrz : (r : ℤ) • zbar p q r = cbar p q r := by
    simpa using r_z_eq_c p q r
  change (d : ℤ) •
      (A • cbar p q r +
       Bx • xbar p q r +
       By • ybar p q r +
       Bz • zbar p q r)
      = omega p q r
  rw [smul_add, smul_add, smul_add]
  rw [← smul_smul, ← smul_smul, ← smul_smul, ← smul_smul]
  rw [← hA, ← hBx, ← hBy, ← hBz]
  simp only [sub_smul, one_smul, add_smul]
  rw [mul_smul, hpx, mul_smul, hqy, mul_smul, hrz]
  simp [omega]
  abel

/-- Final uniqueness statement in the paper's form. -/
theorem theorem11_final_uniqueness
    (p q r N dmax δ : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (hδpos : 0 < δ)
    (hcop : Nat.Coprime δ N)
    (τ ϖ : GradingGroup p q r)
    (hδ : δ ∣ dmax)
    (hτ : δ • τ = omega p q r)
    (hϖ : dmax • ϖ = omega p q r) :
    τ = (dmax / δ) • ϖ := by
  exact theorem11_proves_uniqueness
    p q r N dmax δ hp hq hr hδpos hcop τ ϖ hδ hτ hϖ

end FractionalTriangles
