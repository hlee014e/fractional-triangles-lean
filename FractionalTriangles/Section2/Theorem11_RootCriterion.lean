import Mathlib
import FractionalTriangles.Arithmetic

namespace FractionalTriangles

/-- Arithmetic condition appearing in Theorem 1.1 of the paper. -/
def RootIndexAdmissible (δ k N : ℕ) : Prop :=
  δ ∣ k ∧ Nat.Coprime δ N

/-- A convenient formal package for the paper's `d_max`:
`d` itself is admissible and every admissible index divides `d`.
This avoids committing yet to a particular executable definition of the maximum. -/
structure IsMaximalRootIndex (d k N : ℕ) : Prop where
  dvd_k : d ∣ k
  coprime_N : Nat.Coprime d N
  universal : ∀ {δ : ℕ}, RootIndexAdmissible δ k N → δ ∣ d

/-- The arithmetic part of Theorem 1.1: admissible indices divide `d_max`. -/
theorem admissible_dvd_dmax {δ d k N : ℕ}
    (hd : IsMaximalRootIndex d k N)
    (hδ : RootIndexAdmissible δ k N) :
    δ ∣ d := by
  exact hd.universal hδ

/-- If `δ ∣ d` and both `d` and `δ` are coprime to `N`, then `δ` is an admissible
root index whenever `d ∣ k`. -/
theorem admissible_of_dvd_dmax {δ d k N : ℕ}
    (hd : IsMaximalRootIndex d k N)
    (hδd : δ ∣ d)
    (hδN : Nat.Coprime δ N) :
    RootIndexAdmissible δ k N := by
  constructor
  · exact dvd_trans hδd hd.dvd_k
  · exact hδN

section AbstractRootScaling

variable {L : Type*} [AddCommGroup L]

/-- Once a maximal root `ϖ` is known, every divisor `δ` of `d` produces a root by scaling.
This is the formal version of `τ = (d/δ) ϖ`. -/
theorem scaled_root_exists
    (ω ϖ : L) (d δ : ℕ)
    (hω : d • ϖ = ω)
    (hδ : δ ∣ d) :
    ∃ τ : L, δ • τ = ω := by
  refine ⟨(d / δ) • ϖ, ?_⟩
  calc
    δ • ((d / δ) • ϖ) = (δ * (d / δ)) • ϖ := by
      simp [smul_smul]
    _ = d • ϖ := by
      rw [Nat.mul_div_cancel' hδ]
    _ = ω := hω

/-- If multiplication by `δ` is injective, a `δ`-th root is unique.  In the paper this
injectivity comes from Lemma 2.1 together with `gcd(δ,N)=1`. -/
theorem root_unique_of_nsmul_injective
    (ω : L) (δ : ℕ)
    (hinj : Function.Injective (fun x : L => δ • x))
    {τ₁ τ₂ : L}
    (h₁ : δ • τ₁ = ω)
    (h₂ : δ • τ₂ = ω) :
    τ₁ = τ₂ := by
  apply hinj
  rw [h₁, h₂]

/-- Abstract form of the existence/uniqueness mechanism in Theorem 1.1.
The two paper-specific inputs still to be formalized are:
(1) necessity: a root implies `δ ∣ k` and `gcd(δ,N)=1`;
(2) injectivity of multiplication by admissible `δ` on the concrete grading group `L`.
-/
theorem abstract_root_criterion
    (ω ϖ : L) (d k N : ℕ)
    (hd : IsMaximalRootIndex d k N)
    (hω : d • ϖ = ω)
    (hnecessary : ∀ (δ : ℕ) (τ : L), δ • τ = ω → RootIndexAdmissible δ k N)
    (hinj : ∀ (δ : ℕ), RootIndexAdmissible δ k N →
      Function.Injective (fun x : L => δ • x))
    (δ : ℕ) :
    (∃! τ : L, δ • τ = ω) ↔ RootIndexAdmissible δ k N := by
  constructor
  · rintro ⟨τ, hτ, _⟩
    exact hnecessary δ τ hτ
  · intro hδ
    have hδd : δ ∣ d := hd.universal hδ
    obtain ⟨τ, hτ⟩ := scaled_root_exists ω ϖ d δ hω hδd
    refine ⟨τ, hτ, ?_⟩
    intro τ' hτ'
    exact root_unique_of_nsmul_injective ω δ (hinj δ hδ) hτ' hτ

end AbstractRootScaling

end FractionalTriangles
