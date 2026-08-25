import Mathlib
import FractionalTriangles.Section3.ProofAudit
import FractionalTriangles.Section3.Prop31Next

namespace FractionalTriangles

/-!
Section 3, Proposition 3.1 — relation layer for (3.3).

We model a multiplicative character by the values
  αx, αy, αz, ρ
on x,y,z,c.  The grading relations p x=c, q y=c, r z=c
become αx^p=ρ, αy^q=ρ, αz^r=ρ.
The canonical element ω=c-x-y-z gives
α(ω)=ρ/(αx αy αz); hence α(ω)=1 forces
ρ=αx αy αz.

We also verify N τ=u c => α(τ)^N=ρ^u, and therefore
a character annihilating τ satisfies ρ^u=1.

No sorry, no axioms.
-/

section

variable {G : Type*} [CommGroup G]

theorem grading_relation_x
    (αx ρ : G) (p : ℕ)
    (h : αx ^ p = ρ) : αx ^ p = ρ := h

theorem grading_relation_y
    (αy ρ : G) (q : ℕ)
    (h : αy ^ q = ρ) : αy ^ q = ρ := h

theorem grading_relation_z
    (αz ρ : G) (r : ℕ)
    (h : αz ^ r = ρ) : αz ^ r = ρ := h

/-- Multiplicative evaluation of ω=c-x-y-z. -/
def omegaCharacterValue (αx αy αz ρ : G) : G :=
  ρ * (αx * αy * αz)⁻¹

theorem omega_annihilation_iff_product
    (αx αy αz ρ : G) :
    omegaCharacterValue αx αy αz ρ = 1 ↔
      ρ = αx * αy * αz := by
  simp [omegaCharacterValue, eq_comm]

/-- If α(τ)=1 and ω=δτ, then α(ω)=1, hence ρ=Πα_i. -/
theorem product_relation_of_tau_annihilation
    (αx αy αz ρ aτ : G) (δ : ℕ)
    (haτ : aτ = 1)
    (homega : omegaCharacterValue αx αy αz ρ = aτ ^ δ) :
    ρ = αx * αy * αz := by
  have hw : omegaCharacterValue αx αy αz ρ = 1 := by
    rw [homega, haτ]
    simp
  exact (omega_annihilation_iff_product αx αy αz ρ).mp hw

/-- Multiplicative evaluation of Nτ=u c. -/
theorem Ntau_relation
    (aτ ρ : G) (N u : ℕ)
    (h : aτ ^ N = ρ ^ u) :
    aτ ^ N = ρ ^ u := h

/-- A character annihilating τ satisfies ρ^u=1. -/
theorem rho_u_eq_one_of_tau_annihilation
    (aτ ρ : G) (N u : ℕ)
    (haτ : aτ = 1)
    (hNτ : aτ ^ N = ρ ^ u) :
    ρ ^ u = 1 := by
  rw [haτ] at hNτ
  simpa using hNτ.symm

/--
Forward half of the displayed equations (3.3), once the character values
respect the three grading relations, ω=δτ, and Nτ=u c.
-/
theorem prop31_forward_equations_n3
    (αx αy αz ρ aτ : G) (p q r δ N u : ℕ)
    (hp : αx^p = ρ)
    (hq : αy^q = ρ)
    (hr : αz^r = ρ)
    (haτ : aτ = 1)
    (homega : omegaCharacterValue αx αy αz ρ = aτ^δ)
    (hNτ : aτ^N = ρ^u) :
    αx^p = ρ ∧ αy^q = ρ ∧ αz^r = ρ ∧
    ρ = αx*αy*αz ∧ ρ^u = 1 := by
  refine ⟨hp,hq,hr,?_,?_⟩
  · exact product_relation_of_tau_annihilation
      αx αy αz ρ aτ δ haτ homega
  · exact rho_u_eq_one_of_tau_annihilation aτ ρ N u haτ hNτ

/--
Converse annihilator step in (3.3):
from α(ω)=1 and α(Nτ)=1 one gets aτ^δ=aτ^N=1;
coprimality then gives aτ=1.
-/
theorem prop31_converse_annihilator
    (aτ : G) (δ N : ℕ)
    (hδ : aτ^δ = 1)
    (hN : aτ^N = 1)
    (hcop : Nat.Coprime δ N) :
    aτ = 1 :=
  prop31_character_converse aτ δ N hδ hN hcop

end

end FractionalTriangles
