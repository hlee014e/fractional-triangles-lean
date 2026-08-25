import Mathlib
import FractionalTriangles.Section3.ActualCharacter
import FractionalTriangles.Section3.Prop31Relations

namespace FractionalTriangles

/-!
# Section 3, Proposition 3.1 — actual G_tau characterization

NEW target only.

Paper p. 6, equation (3.3):
  G_tau = { diag(alpha_1,alpha_2,alpha_3) :
            alpha_i^{p_i}=rho:=prod alpha_j, rho^u=1 }.

Here we work with an actual multiplicative character
  χ : L(p,q,r) → G
of the concrete grading group already formalized in Section 2.

Assumptions corresponding exactly to the paper setup:
  δ • τ = ω,
  N • τ = u • c,
  gcd(δ,N)=1.

We prove:
  χ(τ)=1
iff
  rho = alpha_x alpha_y alpha_z  and  rho^u=1.

The three equations alpha_x^p=rho, alpha_y^q=rho, alpha_z^r=rho
are already automatic for every actual character by
`Section3_ActualCharacter.lean`, so they are included in the final packaged
statement without being assumed.

No `sorry`, no axioms.
-/

section

variable {G : Type*} [CommGroup G]

/-- Character value of a grading-group element, unwrapped from `Multiplicative`. -/
def charVal {p q r : ℕ}
    (χ : GradingCharacter p q r G)
    (v : GradingGroup p q r) : G :=
  (χ v).toMul

@[simp] theorem charVal_zero {p q r : ℕ}
    (χ : GradingCharacter p q r G) :
    charVal χ (0 : GradingGroup p q r) = 1 := by
  rfl

/-- Additive multiplication in L becomes powers under a multiplicative character. -/
theorem charVal_nsmul {p q r : ℕ}
    (χ : GradingCharacter p q r G)
    (n : ℕ) (v : GradingGroup p q r) :
    charVal χ (n • v) = (charVal χ v)^n := by
  simp [charVal]

/-- The root equation δτ=ω gives χ(τ)^δ = χ(ω). -/
theorem character_root_equation
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (χ : GradingCharacter p q r G)
    (hroot : δ • τ = omega p q r) :
    (charVal χ τ)^δ = charVal χ (omega p q r) := by
  rw [← charVal_nsmul χ δ τ, hroot]

/-- The equation Nτ=u c gives χ(τ)^N = rho^u with rho=χ(c). -/
theorem character_Ntau_equation
    (p q r N u : ℕ)
    (τ : GradingGroup p q r)
    (χ : GradingCharacter p q r G)
    (hNtau : N • τ = u • cbar p q r) :
    (charVal χ τ)^N = (charC χ)^u := by
  rw [← charVal_nsmul χ N τ, hNtau]
  simpa [charVal, charC] using charVal_nsmul χ u (cbar p q r)

/-- Actual χ(ω) equals the character-value formula rho/(alpha_x alpha_y alpha_z). -/
theorem actual_omega_value_formula
    (p q r : ℕ)
    (χ : GradingCharacter p q r G) :
    charVal χ (omega p q r) =
      omegaCharacterValue (charX χ) (charY χ) (charZ χ) (charC χ) := by
  simp [charVal, omegaCharacterValue, charX, charY, charZ, charC, omega]
  abel

/-- Forward implication of (3.3) for an actual character. -/
theorem actual_Gtau_forward
    (p q r δ N u : ℕ)
    (τ : GradingGroup p q r)
    (χ : GradingCharacter p q r G)
    (hroot : δ • τ = omega p q r)
    (hNtau : N • τ = u • cbar p q r)
    (hτ : charVal χ τ = 1) :
    charC χ = charX χ * charY χ * charZ χ ∧
    (charC χ)^u = 1 := by
  constructor
  ·
    have hw : charVal χ (omega p q r) = 1 := by
      rw [← character_root_equation p q r δ τ χ hroot, hτ]
      simp
    rw [actual_omega_value_formula p q r χ] at hw
    exact (omega_annihilation_iff_product
      (charX χ) (charY χ) (charZ χ) (charC χ)).mp hw
  ·
    have hN := character_Ntau_equation p q r N u τ χ hNtau
    rw [hτ] at hN
    simpa using hN.symm

/-- Converse implication of (3.3) for an actual character. -/
theorem actual_Gtau_converse
    (p q r δ N u : ℕ)
    (τ : GradingGroup p q r)
    (χ : GradingCharacter p q r G)
    (hroot : δ • τ = omega p q r)
    (hNtau : N • τ = u • cbar p q r)
    (hcop : Nat.Coprime δ N)
    (hprod : charC χ = charX χ * charY χ * charZ χ)
    (hrho : (charC χ)^u = 1) :
    charVal χ τ = 1 := by
  have hw : charVal χ (omega p q r) = 1 := by
    rw [actual_omega_value_formula p q r χ]
    exact (omega_annihilation_iff_product
      (charX χ) (charY χ) (charZ χ) (charC χ)).2 hprod
  have hδ : (charVal χ τ)^δ = 1 := by
    rw [character_root_equation p q r δ τ χ hroot, hw]
  have hN : (charVal χ τ)^N = 1 := by
    rw [character_Ntau_equation p q r N u τ χ hNtau, hrho]
  exact group_element_eq_one_of_coprime_powers
    (charVal χ τ) δ N hcop hδ hN

/--
Actual-character version of the displayed description (3.3), n=3.
The three p_i-power relations are consequences of the concrete grading group,
not hypotheses.
-/
theorem actual_Gtau_characterization
    (p q r δ N u : ℕ)
    (τ : GradingGroup p q r)
    (χ : GradingCharacter p q r G)
    (hroot : δ • τ = omega p q r)
    (hNtau : N • τ = u • cbar p q r)
    (hcop : Nat.Coprime δ N) :
    charVal χ τ = 1 ↔
      (charX χ)^p = charC χ ∧
      (charY χ)^q = charC χ ∧
      (charZ χ)^r = charC χ ∧
      charC χ = charX χ * charY χ * charZ χ ∧
      (charC χ)^u = 1 := by
  constructor
  · intro hτ
    have hp := actual_character_px_eq_c p q r χ
    have hq := actual_character_qy_eq_c p q r χ
    have hr := actual_character_rz_eq_c p q r χ
    have hrest := actual_Gtau_forward p q r δ N u τ χ hroot hNtau hτ
    exact ⟨hp, hq, hr, hrest.1, hrest.2⟩
  · rintro ⟨_, _, _, hprod, hrho⟩
    exact actual_Gtau_converse p q r δ N u τ χ hroot hNtau hcop hprod hrho

end

end FractionalTriangles
