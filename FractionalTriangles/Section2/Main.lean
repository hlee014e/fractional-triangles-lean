import Mathlib
import FractionalTriangles.Section2.GradingGroup
import FractionalTriangles.Section2.ScaledDegree
import FractionalTriangles.Section2.Equation22_Generators
import FractionalTriangles.Section2.Equation22
import FractionalTriangles.Section2.Lemma21_Torsion
import FractionalTriangles.Section2.Lemma21
import FractionalTriangles.Section2.Theorem11_RootCriterion

namespace FractionalTriangles

/-!
# Section 2 — Grading group and roots of the dualizing element

This file consolidates the Lean-checked part of Section 2 of the paper
"Fractional Triangle Hypersurfaces: Automatic Cox Models and Divisor Classification".

Paper location: pp. 5–6, equations (2.1)–(2.7), Lemma 2.1, and the proof of Theorem 1.1.

What is fully checked here (with no `sorry`):
* the concrete grading group L(p,q,r);
* the defining relations p x = c, q y = c, r z = c;
* the dualizing element ω = c-x-y-z;
* the scaled degree map N·deg;
* equation (2.2) for every element of L;
* the consequence that degree-zero elements are killed by N;
* Lemma 2.1: if gcd(e,N)=1, multiplication by e on L is injective;
* the abstract scaling/uniqueness part of Theorem 1.1 once a maximal root is supplied.

The only part of the printed proof not yet made concrete in Lean is the quotient
identification (2.4), L/Zc ≃ Z/p ⊕ Z/q ⊕ Z/r, and the explicit formula (2.6) for the
maximal root.  Those are isolated below as the next two targets rather than hidden
behind `sorry` or axioms.
-/

/-- Equation (2.2), restated with the paper's notation `N*deg` encoded by `scaledDegree`. -/
theorem section2_eq_2_2
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (v : GradingGroup p q r) :
    N • v = (scaledDegree p q r N hp hq hr v) • cbar p q r := by
  exact eq22_all p q r N hp hq hr v

/-- Degree-zero elements are N-torsion; this is the torsion-exponent consequence after (2.2). -/
theorem section2_degree_zero_killed_by_N
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (v : GradingGroup p q r)
    (hdeg : scaledDegree p q r N hp hq hr v = 0) :
    N • v = 0 := by
  exact killed_by_N_of_scaledDegree_zero p q r N hp hq hr v hdeg

/-- Lemma 2.1 in the paper. -/
theorem section2_lemma_2_1
    (p q r N e : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (hepos : 0 < e)
    (hcop : Nat.Coprime e N) :
    Function.Injective (fun v : GradingGroup p q r => e • v) := by
  exact lemma21_mul_injective p q r N e hp hq hr hepos hcop

/--
The already checked abstract final step of Theorem 1.1:
from a maximal root `d • ϖ = ω`, every divisor δ of d gives a δ-th root.
-/
theorem section2_root_from_divisor
    (p q r d δ : ℕ)
    (ϖ : GradingGroup p q r)
    (hmax : d • ϖ = omega p q r)
    (hδ : δ ∣ d) :
    ∃ τ : GradingGroup p q r, δ • τ = omega p q r := by
  exact scaled_root_exists (omega p q r) ϖ d δ hmax hδ

/--
The already checked uniqueness mechanism used at the end of Theorem 1.1.
-/
theorem section2_root_unique
    (p q r N δ : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (hδpos : 0 < δ)
    (hcop : Nat.Coprime δ N)
    {τ₁ τ₂ : GradingGroup p q r}
    (h₁ : δ • τ₁ = omega p q r)
    (h₂ : δ • τ₂ = omega p q r) :
    τ₁ = τ₂ := by
  apply section2_lemma_2_1 p q r N δ hp hq hr hδpos hcop
  rw [h₁, h₂]

end FractionalTriangles
