import Mathlib
import FractionalTriangles.Section3_GtauCharacterization
import FractionalTriangles.Section3_Prop31OrderInvariants

namespace FractionalTriangles

/-!
# Section 3, Proposition 3.1 — invariant degree criterion for (3.5)

NEW target only.

Let Q = L / Z tau.  A homogeneous degree ell determines a class q in Q.
The diagonal character action on a homogeneous vector of degree ell is scalar
multiplication by χ(q).  Thus invariance under every character is equivalent
to χ(q)=1 for every χ.

Assuming the standard character-separation property for the finite abelian
quotient, this is equivalent to q=0, i.e. ell lies in Z tau.

This is the group/graded-piece core of the paper's sentence preceding (3.5).
No `sorry`, no axioms.
-/

section

variable {Q K V : Type*}
variable [AddCommGroup Q] [CommGroup K]
variable [AddCommGroup V] [Module ℤ V]

/-- Multiplicative characters of a quotient degree group. -/
abbrev QuotientCharacter (Q K : Type*) [AddCommGroup Q] [CommGroup K] :=
  Q →+ Multiplicative K

/--
Character separation in multiplicative notation: every nonzero quotient class
is detected by some character.
-/
def MulCharactersSeparatePoints
    (Chars : Set (QuotientCharacter Q K)) : Prop :=
  ∀ q : Q, q ≠ 0 → ∃ χ ∈ Chars, (χ q).toMul ≠ 1

/-- Core annihilator criterion. -/
theorem all_characters_trivial_iff_zero
    (Chars : Set (QuotientCharacter Q K))
    (hsep : MulCharactersSeparatePoints Chars)
    (q : Q) :
    (∀ χ ∈ Chars, (χ q).toMul = 1) ↔ q = 0 := by
  constructor
  · intro hall
    by_contra hq
    rcases hsep q hq with ⟨χ, hχ, hdet⟩
    exact hdet (hall χ hχ)
  · intro hq
    subst q
    intro χ hχ
    simp

/--
If `classOf ell = 0` iff ell belongs to Z tau, then invariance under every
character is equivalent to membership in Z tau.
-/
theorem invariant_degree_iff_mem_Ztau
    {L : Type*} [AddCommGroup L]
    (classOf : L →+ Q)
    (tau : L)
    (Chars : Set (QuotientCharacter Q K))
    (hsep : MulCharactersSeparatePoints Chars)
    (hker : ∀ ell : L,
      classOf ell = 0 ↔ ell ∈ AddSubgroup.zmultiples tau)
    (ell : L) :
    (∀ χ ∈ Chars, (χ (classOf ell)).toMul = 1) ↔
      ell ∈ AddSubgroup.zmultiples tau := by
  rw [all_characters_trivial_iff_zero Chars hsep (classOf ell)]
  exact hker ell

end

/-!
For the concrete quotient Q=L/Ztau, `hker` is supplied by the quotient map
itself.  The only genuinely external algebra fact still needed at this layer
is character separation for finite abelian groups over a coefficient group
containing enough roots of unity (the paper uses C^*).

After that, identifying the direct sum of homogeneous pieces with degrees in
Ztau with R(p,tau) is definitional/graded-ring infrastructure.
-/

end FractionalTriangles
