import Mathlib
import FractionalTriangles.Section4_Early

namespace FractionalTriangles
namespace Section4Lemma42

/-!
# Lemma 4.2 — Lean formalization boundary

Paper: Lemma 4.2, pp. 7–8 of `fractional_triangles_v04`.

The current Mathlib/project does not provide the full stack-theoretic
infrastructure needed to define the Geigle–Lenzing DM curve, residual gerbes,
stacky Proj, or the normalization argument in the exact form used in the paper.

This file therefore formalizes the arithmetic core without `sorry` or axioms,
and records the exact geometric inputs that a future full formalization must
supply.
-/

/-- A natural number `d` has the universal property of the gcd of a set `Σ`:
    it divides every member, and every common divisor divides `d`. -/
def IsSetGCD (Σ : Set ℕ) (d : ℕ) : Prop :=
  (∀ m, m ∈ Σ → d ∣ m) ∧
  ∀ e, (∀ m, m ∈ Σ → e ∣ m) → e ∣ d

/-- To prove that `p` is the gcd of a (possibly infinite) set of degrees, it is
    enough to know that every degree is divisible by `p` and that two degrees
    in the set have gcd exactly `p`.

    In the paper, Serre vanishing gives all sufficiently large multiples of
    `p_i`; choosing two suitable such multiples supplies the two witnesses.
-/
theorem isSetGCD_of_two_witnesses
    (Σ : Set ℕ) (p a b : ℕ)
    (hall : ∀ m, m ∈ Σ → p ∣ m)
    (ha : a ∈ Σ) (hb : b ∈ Σ)
    (hg : Nat.gcd a b = p) :
    IsSetGCD Σ p := by
  constructor
  · exact hall
  · intro e he
    rw [← hg]
    exact Nat.dvd_gcd (he a ha) (he b hb)

/-- The root-character arithmetic from Lemma 4.2: if
    `δ s_i ≡ -1 (mod p_i)`, then `s_i` is coprime to `p_i`.
    This theorem was already Lean-checked in `Section4_Early`. -/
theorem root_character_coprime
    (δ p : ℕ) (s : ℤ)
    (h : Int.ModEq p ((δ : ℤ) * s) (-1 : ℤ)) :
    Nat.Coprime (Int.natAbs s) p := by
  exact Section4.root_character_is_unit δ p s h

/-!
## Exact external geometric inputs needed for a full Lean proof of Lemma 4.2

1. **Geigle–Lenzing Cox identification**
   For every `v ∈ L`,
   `T_v ≃ H^0(X, O_X(v))`.
   Equivalently, sections are homogeneous functions on the punctured Cox cone;
   normality plus codimension two extends them across the vertex.

2. **Stacky Proj / quotient-stack stabilizer formula**
   For `Y = Proj^st S` and
   `Σ_P = {m ≥ 1 | ∃ s ∈ H^0(X,L^m), s(P) ≠ 0}`,
   the stabilizer is
   `{λ ∈ G_m | λ^m = 1 for every m ∈ Σ_P} = μ_{gcd(Σ_P)}`.

3. **Residual gerbe and evaluation exact sequence**
   At the stacky point `P_i`, with residual gerbe `G_i ≃ B μ_{p_i}` and
   ideal sheaf `I_i`,
   `0 → I_i L^m → L^m → L^m|_{G_i} → 0`.

4. **Character obstruction**
   The character `s_i` of `L|_{G_i}` satisfies
   `δ s_i ≡ -1 (mod p_i)`; hence it is faithful.  Therefore a section
   nonzero at `P_i` can occur only if `p_i ∣ m`.
   The coprimality part is formalized above.

5. **Serre vanishing after descent to the coarse P^1**
   A sufficiently divisible power of `L` descends to an ample line bundle on
   the coarse `P^1`; for every sufficiently large multiple of `p_i`,
   `H^1(X, I_i L^m)=0`.  Hence evaluation is surjective and those multiples
   belong to `Σ_{P_i}`.

6. **Coarse reconstruction**
   For `M` divisible by `p,q,r`, the `M`-th Veronese section ring reconstructs
   the coarse `P^1`, so the coarse map `X → Proj^st S` is an isomorphism.

7. **Final stack-theoretic normalization step**
   The natural map is representable, proper and quasifinite, hence finite; it
   is birational, and the target is normal.  A finite representable birational
   morphism to a normal DM stack is an isomorphism.

Once these seven geometric results are available as formal theorems, the
printed Lemma 4.2 can be formalized without adding any mathematical argument.
-/

end Section4Lemma42
end FractionalTriangles
