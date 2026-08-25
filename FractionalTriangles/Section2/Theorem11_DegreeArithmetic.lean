import Mathlib
import FractionalTriangles.Section2.Main

namespace FractionalTriangles

/-!
Paper block: Section 2, PDF pp. 3–4 in `higher_canonical_roots_v03(2).pdf`
(the printed page footer shows page 4 at the Lemma 2.1 / Theorem 1.1 transition).
Source lines: equation (2.4), Lemma 2.1, proof of Theorem 1.1, equations (2.5),(2.6).

This file follows the final paragraph of Theorem 1.1 literally, including
  δ (τ - (dmax/δ) ϖ) = 0
and the uniqueness deduction.

The arithmetic construction of the explicit ϖ in (2.6) is represented by its
precise hypotheses (dmax • ϖ = ω); no `sorry` or axiom is introduced.
The remaining future formalization target is the derivation of that hypothesis
from the b_i congruences in (2.6), and the quotient isomorphism (2.4).
-/

/-- Literal paper identity before the words "proves uniqueness". -/
theorem theorem11_uniqueness_identity
    (p q r dmax δ : ℕ)
    (τ ϖ : GradingGroup p q r)
    (hδ : δ ∣ dmax)
    (hτ : δ • τ = omega p q r)
    (hϖ : dmax • ϖ = omega p q r) :
    δ • (τ - (dmax / δ) • ϖ) = 0 := by
  rcases hδ with ⟨m, hm⟩
  subst dmax
  simp only [Nat.mul_div_left, smul_sub, Nat.mul_smul]
  rw [hτ, hϖ]
  exact sub_self _

/-- The paper's final uniqueness sentence, now as one concrete Lean theorem. -/
theorem theorem11_proves_uniqueness
    (p q r N dmax δ : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (hδpos : 0 < δ)
    (hcop : Nat.Coprime δ N)
    (τ ϖ : GradingGroup p q r)
    (hδ : δ ∣ dmax)
    (hτ : δ • τ = omega p q r)
    (hϖ : dmax • ϖ = omega p q r) :
    τ = (dmax / δ) • ϖ := by
  apply section2_lemma_2_1 p q r N δ hp hq hr hδpos hcop
  have hzero := theorem11_uniqueness_identity p q r dmax δ τ ϖ hδ hτ hϖ
  simpa [smul_sub] using hzero

/-- The existence half after construction of the maximal root. -/
theorem theorem11_root_from_maximal_root
    (p q r dmax δ : ℕ)
    (ϖ : GradingGroup p q r)
    (hδ : δ ∣ dmax)
    (hϖ : dmax • ϖ = omega p q r) :
    δ • ((dmax / δ) • ϖ) = omega p q r := by
  rcases hδ with ⟨m, hm⟩
  subst dmax
  simp only [Nat.mul_div_left, Nat.mul_smul]
  exact hϖ

/-- Divisibility of k from the degree equation, isolated as the integer arithmetic used in the first paragraph. -/
theorem theorem11_delta_dvd_k_from_degree
    (δ k t : ℕ) (hk : k = δ * t) : δ ∣ k := by
  exact ⟨t, hk.symm⟩

end FractionalTriangles
