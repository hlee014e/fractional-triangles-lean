import Mathlib
import FractionalTriangles.Section5.Prop51

namespace FractionalTriangles
namespace Section5

/-!
# Section 5 — Table 3, Lemma 5.4, Proposition 5.5 numerical identities,
# and Theorem 5.6 divisor parametrization

Paper pp. 18–21.

This bundle focuses on the arithmetic spine:
* Table 3 delta-equations;
* the elementary inequalities in Lemma 5.4;
* the numerical identity (5.2);
* the completed-product identities (5.3)–(5.4);
* the FFF divisor parametrization identity.

No `sorry`, no axioms.
-/

/-! ## Table 3 delta equations -/

theorem table3_FFF_delta
    (α β γ δ : ℤ)
    (hδ : δ = α*β*γ - α*β - α*γ - β*γ) :
    α*β*γ - α*β - α*γ - β*γ = δ := by
  linarith

theorem table3_C2F_rewrite
    (α β γ δ : ℤ)
    (h : γ*(α-1)*(β-1) = α*β + δ) :
    (γ-1)*(α-1)*(β-1) = (α-1)+(β-1)+δ+1 := by
  nlinarith

theorem table3_L2F_rewrite
    (α β γ δ : ℤ)
    (h : γ*(α-1)*(β-1) = α*β - 1 + δ) :
    (γ-1)*(α-1)*(β-1) = (α-1)+(β-1)+δ := by
  nlinarith

theorem table3_C3_rewrite
    (α β γ δ : ℤ)
    (h : γ*(α-1)*(β-1) = α*β - α + 1 + δ) :
    (γ-1)*(α-1)*(β-1) = (β-1)+δ+1 := by
  nlinarith

theorem table3_L3_rewrite
    (α β γ δ : ℤ)
    (h : γ*(α-1)*(β-1) = α*β - α - β + 2 + δ) :
    (γ-1)*(α-1)*(β-1) = δ+1 := by
  nlinarith

/-! ## Lemma 5.4 elementary bounds -/

/--
If A,B ≥ 2 and
  (A-1)(B-1) ≤ δ+2,
then A,B ≤ δ+3.
-/
theorem bound_AB_first
    (A B δ : ℕ)
    (hA : 2 ≤ A) (hB : 2 ≤ B)
    (h : (A-1)*(B-1) ≤ δ+2) :
    A ≤ δ+3 ∧ B ≤ δ+3 := by
  constructor
  · have hmul : A - 1 ≤ (A-1)*(B-1) := by
      exact Nat.le_mul_of_pos_right (A-1) (by omega)
    omega
  · have hmul : B - 1 ≤ (A-1)*(B-1) := by
      exact Nat.le_mul_of_pos_left (B-1) (by omega)
    omega

/--
From (A-1)B ≤ δ+1 and B ≥ 1 one gets A ≤ δ+2.
-/
theorem bound_A_third
    (A B δ : ℕ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (h : (A-1)*B ≤ δ+1) :
    A ≤ δ+2 := by
  have hmul : A - 1 ≤ (A-1)*B := by
    exact Nat.le_mul_of_pos_right (A-1) hB
  omega

/--
FFF α=2 case:
  (β-2)(γ-2)=δ+4
implies β,γ ≤ δ+6.
-/
theorem fff_alpha_two_bound
    (β γ δ : ℕ)
    (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (h : (β-2)*(γ-2)=δ+4) :
    β ≤ δ+6 ∧ γ ≤ δ+6 := by
  have hβ3 : 3 ≤ β := by
    by_contra hn
    have hβ2 : β = 2 := by omega
    simp [hβ2] at h
  have hγ3 : 3 ≤ γ := by
    by_contra hn
    have hγ2 : γ = 2 := by omega
    simp [hγ2] at h
  constructor
  · have hle : β - 2 ≤ (β-2)*(γ-2) := by
      exact Nat.le_mul_of_pos_right (β-2) (by omega)
    omega
  · have hle : γ - 2 ≤ (β-2)*(γ-2) := by
      exact Nat.le_mul_of_pos_left (γ-2) (by omega)
    omega


/--
FFF, ordered case α,β ≥ 3.

From
  αβγ = αβ + αγ + βγ + δ
one gets γ ≤ δ+3.
-/
theorem fff_ge_three_gamma_bound
    (α β γ δ : ℤ)
    (hα : 3 ≤ α)
    (hβ : 3 ≤ β)
    (hγ : 3 ≤ γ)
    (hδ : 0 ≤ δ)
    (heq :
      α*β*γ = α*β + α*γ + β*γ + δ) :
    γ ≤ δ+3 := by
  have ha : 0 ≤ 2*α-3 := by
    linarith
  have hb : 0 ≤ β-3 := by
    linarith
  have h1 : 0 ≤ (2*α-3)*(β-3) := by
    exact mul_nonneg ha hb
  have h2 : 0 ≤ 3*(α-3) := by
    nlinarith
  have hden :
      α*β ≤ 3*(α*β-α-β) := by
    nlinarith [h1, h2]
  have hab : 0 ≤ (α-3)*(β-3) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hD :
      1 ≤ α*β-α-β := by
    nlinarith [hab]
  have hmain :
      (α*β-α-β)*γ = α*β+δ := by
    nlinarith [heq]
  have hshift :
      (α*β-α-β)*(γ-3) ≤ δ := by
    nlinarith [hmain, hden]
  have hD1 :
      0 ≤ (α*β-α-β)-1 := by
    linarith
  have hg3 :
      0 ≤ γ-3 := by
    linarith
  have hprod :
      0 ≤ ((α*β-α-β)-1)*(γ-3) := by
    exact mul_nonneg hD1 hg3
  have hsmall :
      γ-3 ≤ (α*β-α-β)*(γ-3) := by
    nlinarith [hprod]
  linarith


/--
Full FFF case of Lemma 5.4.

After permuting the exponents so that α ≤ β ≤ γ,
the Table 3 equation implies
  α, β, γ ≤ δ+6.
-/
theorem lemma54_FFF_bound
    (α β γ δ : ℕ)
    (hα : 2 ≤ α)
    (hβ : 2 ≤ β)
    (hγ : 2 ≤ γ)
    (hαβ : α ≤ β)
    (hβγ : β ≤ γ)
    (heq :
      α*β*γ = α*β + α*γ + β*γ + δ) :
    α ≤ δ+6 ∧ β ≤ δ+6 ∧ γ ≤ δ+6 := by
  by_cases ha : α = 2
  · subst α
    have hβsplit : β = (β-2)+2 := by
      omega
    have hγsplit : γ = (γ-2)+2 := by
      omega
    have hprod :
        (β-2)*(γ-2) = δ+4 := by
      rw [hβsplit, hγsplit] at heq
      nlinarith [heq]
    obtain ⟨hβbd, hγbd⟩ :=
      fff_alpha_two_bound β γ δ hβ hγ hprod
    exact ⟨by omega, hβbd, hγbd⟩
  · have hα3 : 3 ≤ α := by
      omega
    have hβ3 : 3 ≤ β := by
      omega
    have hγ3 : 3 ≤ γ := by
      omega
    have hα3Z : (3 : ℤ) ≤ (α : ℤ) := by
      exact_mod_cast hα3
    have hβ3Z : (3 : ℤ) ≤ (β : ℤ) := by
      exact_mod_cast hβ3
    have hγ3Z : (3 : ℤ) ≤ (γ : ℤ) := by
      exact_mod_cast hγ3
    have hδ0Z : (0 : ℤ) ≤ (δ : ℤ) := by
      exact_mod_cast Nat.zero_le δ
    have heqZ :
        (α : ℤ) * (β : ℤ) * (γ : ℤ)
          =
        (α : ℤ) * (β : ℤ)
          + (α : ℤ) * (γ : ℤ)
          + (β : ℤ) * (γ : ℤ)
          + (δ : ℤ) := by
      exact_mod_cast heq
    have hγbdZ :
        (γ : ℤ) ≤ (δ : ℤ)+3 := by
      exact fff_ge_three_gamma_bound
        (α : ℤ) (β : ℤ) (γ : ℤ) (δ : ℤ)
        hα3Z hβ3Z hγ3Z hδ0Z heqZ
    have hγbd :
        γ ≤ δ+3 := by
      exact_mod_cast hγbdZ
    constructor
    · omega
    constructor
    · omega
    · omega


/-!
### Remaining four atomic cases of Lemma 5.4

We use
  A = α-1, B = β-1, t = γ-1,
with A,B,t ≥ 1.
-/

/-- C2F integer core. -/
theorem lemma54_C2F_bound_Z
    (A B t δ : ℤ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (hδ : 0 ≤ δ)
    (heq : t*A*B = A+B+δ+1) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  by_cases hA1 : A = 1
  · subst A
    have heq1 : t*B = B+δ+2 := by
      nlinarith [heq]
    have ht2 : 2 ≤ t := by
      by_contra hn
      have ht1 : t = 1 := by omega
      subst t
      nlinarith [heq1, hδ]
    have hpB : 0 ≤ (t-2)*B := by
      exact mul_nonneg (by linarith) (by linarith)
    have hpT : 0 ≤ (t-1)*(B-1) := by
      exact mul_nonneg (by linarith) (by linarith)
    constructor
    · linarith
    constructor
    · nlinarith [heq1, hpB]
    · nlinarith [heq1, hpT]
  · by_cases hB1 : B = 1
    · subst B
      have heq1 : t*A = A+δ+2 := by
        nlinarith [heq]
      have ht2 : 2 ≤ t := by
        by_contra hn
        have ht1 : t = 1 := by omega
        subst t
        nlinarith [heq1, hδ]
      have hpA : 0 ≤ (t-2)*A := by
        exact mul_nonneg (by linarith) (by linarith)
      have hpT : 0 ≤ (t-1)*(A-1) := by
        exact mul_nonneg (by linarith) (by linarith)
      constructor
      · nlinarith [heq1, hpA]
      constructor
      · linarith
      · nlinarith [heq1, hpT]
    · have hA2 : 2 ≤ A := by omega
      have hB2 : 2 ≤ B := by omega
      have hab : 0 ≤ (A-2)*(B-2) := by
        exact mul_nonneg (by linarith) (by linarith)
      have htAB : 0 ≤ (t-1)*(A*B) := by
        exact mul_nonneg (by linarith)
          (mul_nonneg (by linarith) (by linarith))
      have hbound :
          (A-1)*(B-1) ≤ δ+2 := by
        nlinarith [heq, htAB]
      have hAbound : A ≤ δ+3 := by
        have hp : 0 ≤ (A-1)*(B-2) := by
          exact mul_nonneg (by linarith) (by linarith)
        nlinarith [hbound, hp]
      have hBbound : B ≤ δ+3 := by
        have hp : 0 ≤ (A-2)*(B-1) := by
          exact mul_nonneg (by linarith) (by linarith)
        nlinarith [hbound, hp]
      have hABge : A+B ≤ A*B := by
        nlinarith [hab]
      have hAB1 : 1 ≤ A*B := by
        nlinarith [hab]
      have hpT : 0 ≤ (t-1)*(A*B-1) := by
        exact mul_nonneg (by linarith) (by linarith)
      have htbound : t ≤ δ+2 := by
        nlinarith [heq, hABge, hpT]
      exact ⟨by linarith, by linarith, by linarith⟩

/-- Full C2F case of Lemma 5.4. -/
theorem lemma54_C2F_bound
    (A B t δ : ℕ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (heq : t*A*B = A+B+δ+1) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  have hZ := lemma54_C2F_bound_Z
    (A : ℤ) (B : ℤ) (t : ℤ) (δ : ℤ)
    (by exact_mod_cast hA)
    (by exact_mod_cast hB)
    (by exact_mod_cast ht)
    (by exact_mod_cast Nat.zero_le δ)
    (by exact_mod_cast heq)
  exact_mod_cast hZ

/-- L2F integer core. -/
theorem lemma54_L2F_bound_Z
    (A B t δ : ℤ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (hδ : 0 ≤ δ)
    (heq : t*A*B = A+B+δ) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  by_cases hA1 : A = 1
  · subst A
    have heq1 : t*B = B+δ+1 := by
      nlinarith [heq]
    have ht2 : 2 ≤ t := by
      by_contra hn
      have ht1 : t = 1 := by omega
      subst t
      nlinarith [heq1]
    have hpB : 0 ≤ (t-2)*B := by
      exact mul_nonneg (by linarith) (by linarith)
    have hpT : 0 ≤ (t-1)*(B-1) := by
      exact mul_nonneg (by linarith) (by linarith)
    constructor
    · linarith
    constructor
    · nlinarith [heq1, hpB]
    · nlinarith [heq1, hpT]
  · by_cases hB1 : B = 1
    · subst B
      have heq1 : t*A = A+δ+1 := by
        nlinarith [heq]
      have ht2 : 2 ≤ t := by
        by_contra hn
        have ht1 : t = 1 := by omega
        subst t
        nlinarith [heq1]
      have hpA : 0 ≤ (t-2)*A := by
        exact mul_nonneg (by linarith) (by linarith)
      have hpT : 0 ≤ (t-1)*(A-1) := by
        exact mul_nonneg (by linarith) (by linarith)
      constructor
      · nlinarith [heq1, hpA]
      constructor
      · linarith
      · nlinarith [heq1, hpT]
    · have hA2 : 2 ≤ A := by omega
      have hB2 : 2 ≤ B := by omega
      have hab : 0 ≤ (A-2)*(B-2) := by
        exact mul_nonneg (by linarith) (by linarith)
      have htAB : 0 ≤ (t-1)*(A*B) := by
        exact mul_nonneg (by linarith)
          (mul_nonneg (by linarith) (by linarith))
      have hbound :
          (A-1)*(B-1) ≤ δ+1 := by
        nlinarith [heq, htAB]
      have hAbound : A ≤ δ+2 := by
        have hp : 0 ≤ (A-1)*(B-2) := by
          exact mul_nonneg (by linarith) (by linarith)
        nlinarith [hbound, hp]
      have hBbound : B ≤ δ+2 := by
        have hp : 0 ≤ (A-2)*(B-1) := by
          exact mul_nonneg (by linarith) (by linarith)
        nlinarith [hbound, hp]
      have hABge : A+B ≤ A*B := by
        nlinarith [hab]
      have hAB1 : 1 ≤ A*B := by
        nlinarith [hab]
      have hpT : 0 ≤ (t-1)*(A*B-1) := by
        exact mul_nonneg (by linarith) (by linarith)
      have htbound : t ≤ δ+1 := by
        nlinarith [heq, hABge, hpT]
      exact ⟨by linarith, by linarith, by linarith⟩

/-- Full L2F case of Lemma 5.4. -/
theorem lemma54_L2F_bound
    (A B t δ : ℕ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (heq : t*A*B = A+B+δ) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  have hZ := lemma54_L2F_bound_Z
    (A : ℤ) (B : ℤ) (t : ℤ) (δ : ℤ)
    (by exact_mod_cast hA)
    (by exact_mod_cast hB)
    (by exact_mod_cast ht)
    (by exact_mod_cast Nat.zero_le δ)
    (by exact_mod_cast heq)
  exact_mod_cast hZ

/-- C3 integer core. -/
theorem lemma54_C3_bound_Z
    (A B t δ : ℤ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (hδ : 0 ≤ δ)
    (heq : t*A*B = B+δ+1) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  have hid : B*(t*A-1) = δ+1 := by
    nlinarith [heq]
  have hta : 1 ≤ t*A := by
    have hp : 0 ≤ (t-1)*(A-1) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have hfac : 1 ≤ t*A-1 := by
    by_contra hn
    have hz : t*A-1 = 0 := by omega
    nlinarith [hid, hδ]
  have hpB : 0 ≤ (B-1)*(t*A-1) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hBbd : B ≤ δ+1 := by
    nlinarith [hid, hpB]
  have htaBd : t*A ≤ δ+2 := by
    nlinarith [hid, hB]
  have hpA : 0 ≤ (t-1)*A := by
    exact mul_nonneg (by linarith) (by linarith)
  have hpT : 0 ≤ t*(A-1) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hAbd : A ≤ δ+2 := by
    nlinarith [htaBd, hpA]
  have htbd : t ≤ δ+2 := by
    nlinarith [htaBd, hpT]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Full C3 case of Lemma 5.4. -/
theorem lemma54_C3_bound
    (A B t δ : ℕ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (heq : t*A*B = B+δ+1) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  have hZ := lemma54_C3_bound_Z
    (A : ℤ) (B : ℤ) (t : ℤ) (δ : ℤ)
    (by exact_mod_cast hA)
    (by exact_mod_cast hB)
    (by exact_mod_cast ht)
    (by exact_mod_cast Nat.zero_le δ)
    (by exact_mod_cast heq)
  exact_mod_cast hZ

/-- L3 integer core. -/
theorem lemma54_L3_bound_Z
    (A B t δ : ℤ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (hδ : 0 ≤ δ)
    (heq : t*A*B = δ+1) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  have htB : 1 ≤ t*B := by
    have hp : 0 ≤ (t-1)*(B-1) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have hAB : 1 ≤ A*B := by
    have hp : 0 ≤ (A-1)*(B-1) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have htA : 1 ≤ t*A := by
    have hp : 0 ≤ (t-1)*(A-1) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have hpA : 0 ≤ A*(t*B-1) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hpB : 0 ≤ B*(t*A-1) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hpT : 0 ≤ t*(A*B-1) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hAbd : A ≤ δ+1 := by
    nlinarith [heq, hpA]
  have hBbd : B ≤ δ+1 := by
    nlinarith [heq, hpB]
  have htbd : t ≤ δ+1 := by
    nlinarith [heq, hpT]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Full L3 case of Lemma 5.4. -/
theorem lemma54_L3_bound
    (A B t δ : ℕ)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (ht : 1 ≤ t)
    (heq : t*A*B = δ+1) :
    A+1 ≤ δ+6 ∧ B+1 ≤ δ+6 ∧ t+1 ≤ δ+6 := by
  have hZ := lemma54_L3_bound_Z
    (A : ℤ) (B : ℤ) (t : ℤ) (δ : ℤ)
    (by exact_mod_cast hA)
    (by exact_mod_cast hB)
    (by exact_mod_cast ht)
    (by exact_mod_cast Nat.zero_le δ)
    (by exact_mod_cast heq)
  exact_mod_cast hZ

/-!
Together with `lemma54_FFF_bound`, the five atomic families now give the
uniform exponent box of Lemma 5.4:
  α, β, γ ≤ δ+6.
-/

/-! ## Proposition 5.5 numerical bridge -/

/--
Equation (5.2) is exactly the equality of the positive a-invariant degree
with the orbifold canonical degree.
-/
theorem eq52_positive
    (δ h a b c p q r : ℚ)
    (hEq :
      δ*h/(a*b*c) = 1 - 1/p - 1/q - 1/r)
    (hpos : 0 < 1 - 1/p - 1/q - 1/r) :
    0 < δ*h/(a*b*c) := by
  rw [hEq]
  exact hpos

/-!
The actual Cox monomial identities in Table 4 and the injectivity/Hilbert
function argument of Proposition 5.5 remain algebraic-geometric dependencies.
The degree arithmetic after the Cox identities is handled elsewhere by the
grading-group files.
-/

/-! ## Theorem 5.6 completed products -/

/-- C2F completed product. -/
theorem c2f_complete_product
    (t A B δ : ℤ)
    (h : t*A*B = A+B+δ+1) :
    (t*A-1)*(t*B-1) = t*(δ+1)+1 := by
  calc
    (t*A-1)*(t*B-1)
        = t*(t*A*B) - t*A - t*B + 1 := by ring
    _ = t*(A+B+δ+1) - t*A - t*B + 1 := by rw [h]
    _ = t*(δ+1)+1 := by ring

/-- L2F completed product. -/
theorem l2f_complete_product
    (t A B δ : ℤ)
    (h : t*A*B = A+B+δ) :
    (t*A-1)*(t*B-1) = t*δ+1 := by
  calc
    (t*A-1)*(t*B-1)
        = t*(t*A*B) - t*A - t*B + 1 := by ring
    _ = t*(A+B+δ) - t*A - t*B + 1 := by rw [h]
    _ = t*δ+1 := by ring

/--
FFF completed-product identity from the Table 3 equation.
Set A=α-1, U=A(β-1)-1, V=A(γ-1)-1.
-/
theorem fff_complete_product
    (A β γ δ : ℤ)
    (h :
      (A+1)*β*γ - (A+1)*β - (A+1)*γ - β*γ = δ) :
    (A*(β-1)-1)*(A*(γ-1)-1) = A*δ + (A+1)^2 := by
  calc
    (A*(β-1)-1)*(A*(γ-1)-1)
        =
        A*((A+1)*β*γ - (A+1)*β - (A+1)*γ - β*γ)
          + (A+1)^2 := by ring
    _ = A*δ + (A+1)^2 := by rw [h]

/-- Recovery integrality: U ≡ -1 mod t means t divides U+1. -/
theorem congruence_gives_integral_recovery
    (U t : ℕ)
    (h : U % t = (t-1) % t)
    (ht : 0 < t) :
    t ∣ U+1 := by
  by_cases ht1 : t = 1
  · subst t
    simp
  · have ht2 : 2 ≤ t := by omega
    rw [Nat.dvd_iff_mod_eq_zero]
    have htm1 : (t-1) % t = t-1 := by
      exact Nat.mod_eq_of_lt (by omega)
    rw [htm1] at h
    rw [Nat.add_mod, h]
    have hone : 1 % t = 1 := by
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone]
    have hadd : t - 1 + 1 = t := by omega
    rw [hadd, Nat.mod_self]

/-!
External for the FULL Lemma 5.4 / Proposition 5.5 / Theorem 5.6:
* the atomic classification;
* exact Table 4 Cox lifts and their polynomial identities;
* normality, weighted adjunction, genus-zero/root-stack identification;
* finite torus-map injectivity and Hilbert-function surjectivity;
* the proof that every Cox-invertible ring conversely comes from atomic data.

The arithmetic transformations used to make the divisor enumeration finite
and exact are Lean-checked here.
-/

end Section5
end FractionalTriangles
