import Mathlib
import FractionalTriangles.Section3.Prop31_Eq33_Characterization
import FractionalTriangles.Section3.Prop31Next

namespace FractionalTriangles

/-!
# Section 3 — Proposition 3.1: order and invariant-degree criterion

Paper: p. 6, equations (3.4) and (3.5).

NEW targets only.

We do two things here.

(1) Formalize the finite-cardinality algebra behind
      |L / Z tau| = u * |tors(L)|
once the exact-sequence data are supplied as an actual finite extension.

(2) Formalize the purely group-theoretic invariant-degree criterion:
a homogeneous element of L-degree `ell` is fixed by every character
of L/Z tau exactly when the class of `ell` is zero, PROVIDED characters
separate points of the finite quotient.

The character-separation theorem for finite abelian groups is recorded as an
explicit dependency, not silently assumed as a proved theorem of this file.
No `sorry`; no axioms.
-/

section FiniteExtensionCardinality

variable {A B C : Type*}
variable [Fintype A] [Fintype B] [Fintype C]

/--
Cardinality of a finite short exact sequence, packaged in the form needed for
(3.4). We assume an equivalence A ≃ B × C representing the extension data.
-/
theorem card_of_finite_extension
    (e : A ≃ B × C) :
    Fintype.card A = Fintype.card B * Fintype.card C := by
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod]

/--
Arithmetic completion of (3.4):
if |tors(L)| = pqr/N and the image-index contribution is u,
then |L/Ztau| = μ p q r from u=Nμ.
-/
theorem prop31_cardinality_completion
    (cardQ cardT u p q r N : ℚ) (μ : ℚ)
    (hN : N ≠ 0)
    (hQ : cardQ = u * cardT)
    (hT : cardT = (p*q*r)/N)
    (hu : u = N*μ) :
    cardQ = μ*p*q*r := by
  rw [hQ, hT, hu]
  field_simp [hN]
  ring

end FiniteExtensionCardinality

section CharacterSeparationCriterion

variable {Q G : Type*} [AddCommGroup Q] [CommGroup G]

/--
A family of multiplicative characters separates points if every nonzero class
is detected by at least one character.
-/
def CharactersSeparatePoints
    (Chars : Set (Q →+ Multiplicative G)) : Prop :=
  ∀ q : Q, q ≠ 0 → ∃ χ ∈ Chars, χ q ≠ 0

/--
If characters separate points, being annihilated by every character is
equivalent to being the zero class.

This is the exact abstract group-theoretic statement used in the last sentence
of Proposition 3.1 before (3.5).
-/
theorem fixed_by_all_characters_iff_zero
    (Chars : Set (Q →+ Multiplicative G))
    (hsep : CharactersSeparatePoints Chars)
    (q : Q) :
    (∀ χ ∈ Chars, χ q = 0) ↔ q = 0 := by
  constructor
  · intro hall
    by_contra hq
    rcases hsep q hq with ⟨χ, hχ, hdetect⟩
    exact hdetect (hall χ hχ)
  · intro hq
    subst q
    intro χ hχ
    simp

end CharacterSeparationCriterion

/-!
The remaining ring-theoretic step for (3.5) is now sharply isolated:

* define T as an L-graded ring;
* define the action of G_tau on each homogeneous piece by its character;
* invoke/prove character separation for the finite abelian quotient L/Z tau;
* identify the sum of homogeneous pieces with degree in Z tau with
  R(p,tau).

That last identification is exactly the definition of the Veronese/section
subring in the paper.  It will be the next verification block.
-/

end FractionalTriangles
