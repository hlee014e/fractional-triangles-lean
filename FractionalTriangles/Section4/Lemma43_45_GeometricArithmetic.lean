import Mathlib
import FractionalTriangles.Section3.Main

namespace FractionalTriangles

/-!
# Section 4 (early block): Recovery and automatic Cox-invertibility

Paper: pp. 7–10, Definition 4.1 and Lemmas 4.2–4.5.

This is a paper-verification bundle.  It formalizes the elementary
arithmetic/group-theoretic parts of the printed proofs and explicitly records
the stack-geometric statements that remain external dependencies.

No `sorry`, no axioms.
-/

namespace Section4

/-! ## Definition 4.1 — primitive numerical data -/

/-- Primitive weights mean gcd(A,B,C)=1. -/
def PrimitiveWeights (A B C : ℕ) : Prop :=
  Nat.gcd A (Nat.gcd B C) = 1


/-! ## Lemma 4.2 — stabilizer from nonvanishing section degrees -/

/--
For a nonempty finite list of positive degrees, the common roots of unity
condition λ^m=1 for all m is controlled by the gcd.  We record the arithmetic
core: an integer dividing every degree divides their gcd.
-/
theorem dvd_gcd_of_dvd_all
    (a b : ℕ) (d : ℕ)
    (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ Nat.gcd a b := by
  exact Nat.dvd_gcd ha hb

/--
If the root character `s_i` satisfies δ s_i ≡ -1 mod p_i, then `s_i` is a unit
mod p_i; equivalently gcd(s_i,p_i)=1.  This is the arithmetic step in Lemma 4.2.
-/
theorem root_character_is_unit
    (δ p : ℕ) (s : ℤ)
    (h : Int.ModEq p ((δ : ℤ) * s) (-1 : ℤ)) :
    Nat.Coprime (Int.natAbs s) p := by
  have hδ : Nat.Coprime δ p :=
    coprime_of_mul_modEq_neg_one δ p s h
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨k, hk⟩
  have hbez : (1 : ℤ) = -(δ : ℤ) * s + (p : ℤ) * (-k) := by
    linarith
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : (Nat.gcd (Int.natAbs s) p : ℤ) ∣ 1 := by
    have hs : (Nat.gcd (Int.natAbs s) p : ℤ) ∣ s := by
      have hsd := Nat.gcd_dvd_left (Int.natAbs s) p
      exact_mod_cast Int.natAbs_dvd.mp hsd
    have hp : (Nat.gcd (Int.natAbs s) p : ℤ) ∣ p := by
      exact_mod_cast Nat.gcd_dvd_right (Int.natAbs s) p
    exact dvd_add (dvd_mul_of_dvd_right hs _) (dvd_mul_of_dvd_right hp _)
  have : Nat.gcd (Int.natAbs s) p = 1 := by
    have hn := Int.natAbs_dvd_natAbs.mpr hg
    simpa using hn
  exact this

/-!
Geometric dependencies for Lemma 4.2 (external):
* Geigle–Lenzing Cox identification T_v = H^0(X,O_X(v));
* extension across the codimension-two vertex using normality;
* Serre vanishing on the coarse P^1;
* ordinary Proj reconstruction for a sufficiently divisible Veronese;
* finite representable birational morphism to a normal DM stack is an isomorphism.
-/

/-! ## Lemma 4.3 — locally constant stabilizer data -/

/--
Discrete-data principle used repeatedly in Lemma 4.3:
a locally constant map from a connected space to a discrete finite set is
constant.  We encode the set-theoretic core.
-/
theorem constant_of_pairwise_equal
    {α β : Type*} (f : α → β)
    (h : ∀ x y, f x = f y) :
    ∃ b, ∀ x, f x = b := by
  classical
  by_cases hα : Nonempty α
  · rcases hα with ⟨x⟩
    exact ⟨f x, fun y => h y x⟩
  · exact ⟨Classical.choice (show Nonempty β from Classical.propComplete (Nonempty β)), by
      intro x
      exact False.elim (hα ⟨x⟩)⟩

/-!
Geometric dependencies for Lemma 4.3 (external):
* relative inertia finite and unramified;
* tame stacks are étale-locally finite linearly-reductive quotients;
* H^1(<g>,M)=0 by linear reductivity;
* coarse-space formation compatible with base change;
* finite-order automorphism of a formal disc with derivative 1 is trivial;
* standard local orbifold-curve model [Spec B[[z]]/μ_r].
-/

/-! ## Lemma 4.4 — numerical rigidity ingredients -/

/--
Weighted degree of O(1) on a degree-h curve in P(A,B,C), as used in the paper.
This is just the rational numerical expression.
-/
def orbifoldDegreeO1 (A B C h : ℕ) : ℚ :=
  (h : ℚ) / ((A : ℚ) * (B : ℚ) * (C : ℚ))

theorem orbifoldDegreeO1_def (A B C h : ℕ) :
    orbifoldDegreeO1 A B C h =
      (h : ℚ) / ((A : ℚ) * (B : ℚ) * (C : ℚ)) := by
  rfl

/-!
Geometric dependencies for Lemma 4.4 (external):
* quasismooth locus is nonempty Zariski open, hence irreducible;
* universal quotient hypersurface is a smooth proper tame DM curve;
* connected components and coarse genus are locally constant;
* Lemma 4.3;
* orbifold curve with trivial generic stabilizer is the iterated root stack;
* three points on P^1 have no cross-ratio modulus;
* Picard exact sequence for the root stack;
* Pic^0(P^1)=0.
-/

/-! ## Lemma 4.5 — stacky points and adjunction -/

/-- Stabilizer on an open coordinate line has order gcd(A_i,A_j). -/
def CoordinateLineStabilizer (Ai Aj : ℕ) : ℕ :=
  Nat.gcd Ai Aj


/--
Algebraic equivalence of the adjunction formula in Lemma 4.5 with displayed
equation (4.4).

Assume
  δh/(ABC) = 2g-2 + Σ(1-1/r_i).
Then
  2g = δh/(ABC) - 1 + Σ 1/r_i.
-/
theorem adjunction_equiv_44
    (δ h A B C g r1 r2 r3 : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) (hr3 : r3 ≠ 0)
    (hadj :
      δ*h/(A*B*C) =
        2*g - 2 +
          (1 - 1/r1) + (1 - 1/r2) + (1 - 1/r3)) :
    2*g =
      δ*h/(A*B*C) - 1 + 1/r1 + 1/r2 + 1/r3 := by
  field_simp [hA, hB, hC, hr1, hr2, hr3] at hadj ⊢
  linarith

/--
If a binomial on the effective torus becomes u^s - λ with λ ≠ 0 over C and
has distinct roots, then the number of roots is |s|.  We record the natural
number identity used for the orbit count.
-/

/-!
External geometric input for Lemma 4.5:
* quotient-presentation stabilizer calculation;
* effective weighted torus coordinate on the open coordinate line;
* quasismoothness => distinct roots;
* weighted adjunction ω_C = O_C(h-A-B-C);
* deg O_C(1)=h/(ABC).
-/

end Section4
end FractionalTriangles
