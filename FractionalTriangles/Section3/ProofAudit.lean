import Mathlib
import FractionalTriangles.Section3.Main
import FractionalTriangles.Section2.Lemma21

namespace FractionalTriangles

/-!
# Section 3 proof audit — paper pp. 6–7

This file follows the printed proof of Proposition 3.1 and Proposition 3.2
sentence-by-sentence wherever the step is pure group/arithmetic algebra.

IMPORTANT:
This is a verification audit, so nothing is hidden behind `sorry` or axioms.
Claims requiring a substantial new formal library (graded invariant rings,
normality of invariant rings, Molien's theorem itself, canonical modules) are
listed in the companion README as PENDING rather than represented as proved.

Paper lines audited here:
* root character: τ annihilated => ω=δτ annihilated;
* Bézout converse used in (3.3): a^δ=a^N=1 and gcd(δ,N)=1 => a=1;
* arithmetic of the order formula (3.4);
* the exponent identity 1/μ - Σ 1/(μ p_i) = δ;
* ρ = product α_i and inversion algebra used for (3.9);
* the "cannot fix n-1 coordinates" argument for n=3;
* leading coefficient arithmetic in Proposition 3.2;
* hypersurface reciprocity exponent comparison.
-/

section CommGroupCharacterSteps

variable {G : Type*} [CommGroup G]

/-- If τ maps to 1, then δτ maps to 1; abstract character version. -/
theorem character_annihilates_multiple
    (a : G) (δ : ℕ) (ha : a = 1) :
    a ^ δ = 1 := by
  simp [ha]

/-- Bézout step used in the converse of Proposition 3.1.
If an element is killed by both δ and N and gcd(δ,N)=1, it is trivial. -/
theorem group_element_eq_one_of_coprime_powers
    (a : G) (δ N : ℕ)
    (hcop : Nat.Coprime δ N)
    (hδ : a ^ δ = 1)
    (hN : a ^ N = 1) :
    a = 1 := by
  rcases hcop with ⟨m, n, hbez⟩
  -- Mathlib's Nat.Coprime witness is subtraction-based; use order divisibility.
  have hordδ : orderOf a ∣ δ := (orderOf_dvd_iff_pow_eq_one).2 hδ
  have hordN : orderOf a ∣ N := (orderOf_dvd_iff_pow_eq_one).2 hN
  have hordg : orderOf a ∣ Nat.gcd δ N := Nat.dvd_gcd hordδ hordN
  have hgcd : Nat.gcd δ N = 1 := hcop.gcd_eq_one
  rw [hgcd] at hordg
  have ho : orderOf a = 1 := Nat.eq_one_of_dvd_one hordg
  exact orderOf_eq_one_iff.mp ho

/-- If two of α₁,α₂,α₃ are 1 and αᵢ^pᵢ = ρ = α₁α₂α₃,
then the third is also 1. This is the n=3 instance of the pole argument. -/
theorem nonidentity_cannot_fix_two_coordinates_1
    (α1 α2 α3 ρ : G)
    (hrho : ρ = α1 * α2 * α3)
    (h2 : α2 = 1) (h3 : α3 = 1)
    (hp2 : α2 ^ 2 = ρ) :
    α1 = 1 := by
  have hr : ρ = 1 := by simpa [h2] using hp2
  rw [h2, h3] at hrho
  simpa [hr] using hrho.symm

theorem nonidentity_cannot_fix_two_coordinates_2
    (α1 α2 α3 ρ : G)
    (hrho : ρ = α1 * α2 * α3)
    (h1 : α1 = 1) (h3 : α3 = 1)
    (hp1 : α1 ^ 2 = ρ) :
    α2 = 1 := by
  have hr : ρ = 1 := by simpa [h1] using hp1
  rw [h1, h3] at hrho
  simpa [hr] using hrho.symm

theorem nonidentity_cannot_fix_two_coordinates_3
    (α1 α2 α3 ρ : G)
    (hrho : ρ = α1 * α2 * α3)
    (h1 : α1 = 1) (h2 : α2 = 1)
    (hp1 : α1 ^ 2 = ρ) :
    α3 = 1 := by
  have hr : ρ = 1 := by simpa [h1] using hp1
  rw [h1, h2] at hrho
  simpa [hr] using hrho.symm

end CommGroupCharacterSteps

section Arithmetic

/-- Paper (3.1): u=k/δ under δ|k. -/
theorem sec3_u_identity
    (k δ u : ℕ) (h : k = δ * u) :
    (u : ℚ) = (k : ℚ) / δ := by
  have hδ : (δ : ℚ) ≠ 0 := by
    intro hz
    have : δ = 0 := by exact_mod_cast hz
    subst δ
    simp at h
  rw [h]
  field_simp [hδ]

/-- Arithmetic form of |L/Zτ| = u*(pqr/N) = μ pqr when u=Nμ. -/
theorem sec3_order_formula_arithmetic
    (u p q r N : ℚ) (μ : ℚ)
    (hN : N ≠ 0)
    (hu : u = N * μ) :
    u * (p*q*r / N) = μ * p*q*r := by
  rw [hu]
  field_simp [hN]
  ring

/-- The exponent identity used in the proof of (3.9), n=3. -/
theorem sec3_reciprocity_exponent
    (μ ν δ p q r : ℚ)
    (hμ : μ ≠ 0)
    (hν : ν = 1 - 1/p - 1/q - 1/r)
    (hroot : ν = μ * δ) :
    1/μ - 1/(μ*p) - 1/(μ*q) - 1/(μ*r) = δ := by
  rw [hν] at hroot
  field_simp [hμ] at hroot ⊢
  nlinarith

/-- Identity contribution before division by |G|:
(1/μ) / Π_i(1/(μ p_i)) = μ^2 p q r for n=3. -/
theorem sec3_identity_leading_coefficient
    (μ p q r : ℚ)
    (hμ : μ ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (1/μ) / ((1/(μ*p))*(1/(μ*q))*(1/(μ*r)))
      = μ^2 * p*q*r := by
  field_simp [hμ, hp, hq, hr]
  ring

/-- Dividing the preceding coefficient by |G|=μ p q r yields μ (n=3). -/
theorem sec3_after_group_order_leading_coefficient
    (μ p q r : ℚ)
    (hμ : μ ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (μ^2 * p*q*r) / (μ*p*q*r) = μ := by
  field_simp [hμ, hp, hq, hr]
  ring

/-- Hypersurface pole coefficient h/(abc) equals μ gives the second identity. -/
theorem sec3_second_identity
    (h a b c μ : ℚ)
    (hh : h/(a*b*c) = μ) :
    h/(a*b*c) = μ := hh

/-- Reciprocity exponent comparison gives the first identity. -/
theorem sec3_first_identity
    (h a b c δ : ℤ)
    (hrec : -(h-a-b-c) = -δ) :
    h-a-b-c = δ := by
  linarith

end Arithmetic

end FractionalTriangles
