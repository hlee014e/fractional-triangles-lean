import Mathlib
import FractionalTriangles.Section2.GradingGroup
import FractionalTriangles.Section4.Lemma42Characters

namespace FractionalTriangles
namespace Section4Lemma42Polarization

/-!
# Lemma 4.2 — the polarization O(1)

The root section ring is regraded by

    S_m := T_{m τ}.

Thus degree `1` in the new ℕ-grading corresponds to `τ` in the original
Geigle--Lenzing grading.

Geometrically, for

    Y = Proj^st S,

the natural reconstruction morphism `f : X → Y` satisfies

    f^* O_Y(1) ≃ O_X(τ).

The current project does not formalize stacky Proj or its tautological
line bundle.  We therefore isolate this geometric identification as an
explicit hypothesis and Lean-check its character-theoretic consequences.
-/

/--
Abstract form of the statement

    char_{P_i}(f^* O_Y(1)) = char_{P_i}(O_X(τ)).

The right-hand side is the concrete character of `τ`.
-/
theorem O1_character_eq_tau_character
    {A : Type*} [AddGroup A]
    (χ : A →+ ZMod 1)
    (τ : A)
    (sO1 : ZMod 1)
    (hO1 : sO1 = χ τ) :
    sO1 = χ τ := by
  exact hO1


/--
At the p-stacky point, if the character of O(1) is identified with the
character of τ, then the root equation δτ = ω gives

    δ · char(O(1)) = -1  in Z/pZ.
-/
theorem O1_root_character_X
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (sO1 : ZMod p)
    (hroot : δ • τ = omega p q r)
    (hO1 :
      sO1 =
        Section4Lemma42Characters.charX p q r τ) :
    δ • sO1 = -1 := by
  rw [hO1]
  exact
    Section4Lemma42Characters.root_character_X
      p q r δ τ hroot


/--
The analogous statement at the q-stacky point.
-/
theorem O1_root_character_Y
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (sO1 : ZMod q)
    (hroot : δ • τ = omega p q r)
    (hO1 :
      sO1 =
        Section4Lemma42Characters.charY p q r τ) :
    δ • sO1 = -1 := by
  rw [hO1]
  exact
    Section4Lemma42Characters.root_character_Y
      p q r δ τ hroot


/--
The analogous statement at the r-stacky point.
-/
theorem O1_root_character_Z
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (sO1 : ZMod r)
    (hroot : δ • τ = omega p q r)
    (hO1 :
      sO1 =
        Section4Lemma42Characters.charZ p q r τ) :
    δ • sO1 = -1 := by
  rw [hO1]
  exact
    Section4Lemma42Characters.root_character_Z
      p q r δ τ hroot
/--
Algebraic content of the paper's phrase
"the faithful character of O(1)".

If the O(1)-character `s` satisfies

    δ * s = -1  in Z/pZ,

then multiplication by `s` has trivial kernel:
if `ξ * s = 0`, then `ξ = 0`.

Equivalently, the corresponding character of μ_p is faithful.
-/
theorem O1_character_faithful
    (p δ : ℕ)
    (s : ZMod p)
    (hroot : δ • s = -1) :
    ∀ ξ : ZMod p, ξ * s = 0 → ξ = 0 := by
  intro ξ hξ

  have hδs : (δ : ZMod p) * s = -1 := by
    simpa [nsmul_eq_mul] using hroot

  have hξδs : ξ * ((δ : ZMod p) * s) = 0 := by
    calc
      ξ * ((δ : ZMod p) * s)
          = (δ : ZMod p) * (ξ * s) := by ring
      _ = 0 := by rw [hξ]
      _ = 0 := rfl

  rw [hδs] at hξδs
  simpa using hξδs
/--
If the pulled-back O(1)-character is faithful, then the map on
stabilizers is injective.

This is the group-theoretic step used in Lemma 4.2 before applying
the standard representability criterion for morphisms of
Deligne--Mumford stacks.
-/
theorem stabilizer_map_injective_of_faithful_pullback
    {G H K : Type*}
    [Group G] [Group H] [Group K]
    (φ : G →* H)
    (χ : H →* K)
    (hfaithful : Function.Injective (χ.comp φ)) :
    Function.Injective φ := by
  intro g₁ g₂ hφ
  apply hfaithful
  simp [hφ]
end Section4Lemma42Polarization
end FractionalTriangles
