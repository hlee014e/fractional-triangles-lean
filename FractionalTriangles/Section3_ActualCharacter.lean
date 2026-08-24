import Mathlib
import FractionalTriangles.Eq24
import FractionalTriangles.Section3_Prop31Relations

namespace FractionalTriangles

/-!
# Section 3, Proposition 3.1 — actual grading-character bridge

NEW target only: replace the previously assumed relations
  αx^p=ρ, αy^q=ρ, αz^r=ρ
by consequences of an actual homomorphism α : L → G and the already
formalized relations p*x=c, q*y=c, r*z=c in GradingGroup.

No repetition of the already checked coprime-exponent or rho-product arguments.
No sorry, no axioms.
-/

section

variable {G : Type*} [CommGroup G]

/-- A multiplicative character of the concrete grading group L. -/
abbrev GradingCharacter (p q r : ℕ) (G : Type*) [CommGroup G] :=
  GradingGroup p q r →+ Multiplicative G

/-- Character values used in the paper. -/
def charX {p q r : ℕ} (χ : GradingCharacter p q r G) : G :=
  (χ (xbar p q r)).toMul

def charY {p q r : ℕ} (χ : GradingCharacter p q r G) : G :=
  (χ (ybar p q r)).toMul

def charZ {p q r : ℕ} (χ : GradingCharacter p q r G) : G :=
  (χ (zbar p q r)).toMul

def charC {p q r : ℕ} (χ : GradingCharacter p q r G) : G :=
  (χ (cbar p q r)).toMul

/-- This is no longer a hypothesis: it follows from p*x=c in L. -/
theorem actual_character_px_eq_c
    (p q r : ℕ) (χ : GradingCharacter p q r G) :
    (charX χ)^p = charC χ := by
  have h := congrArg χ (p_x_eq_c p q r)
  simpa [charX, charC] using h

/-- q*y=c gives the second displayed relation. -/
theorem actual_character_qy_eq_c
    (p q r : ℕ) (χ : GradingCharacter p q r G) :
    (charY χ)^q = charC χ := by
  have h := congrArg χ (q_y_eq_c p q r)
  simpa [charY, charC] using h

/-- r*z=c gives the third displayed relation. -/
theorem actual_character_rz_eq_c
    (p q r : ℕ) (χ : GradingCharacter p q r G) :
    (charZ χ)^r = charC χ := by
  have h := congrArg χ (r_z_eq_c p q r)
  simpa [charZ, charC] using h

/--
All three power relations in (3.3), now derived directly from the concrete
grading group rather than supplied as hypotheses.
-/
theorem actual_character_three_power_relations
    (p q r : ℕ) (χ : GradingCharacter p q r G) :
    (charX χ)^p = charC χ ∧
    (charY χ)^q = charC χ ∧
    (charZ χ)^r = charC χ := by
  exact ⟨actual_character_px_eq_c p q r χ,
         actual_character_qy_eq_c p q r χ,
         actual_character_rz_eq_c p q r χ⟩

end

end FractionalTriangles
