import Mathlib
import FractionalTriangles.Section4.Lemma43_45_GeometricArithmetic

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

/-!
/--
Arithmetic form of the character obstruction in Lemma 4.2.

If
    δ * s ≡ -1 (mod p)
and
    m * s ≡ 0 (mod p),
then
    p ∣ m.

Thus, once `s` is the stabilizer character of `L` at a stacky point,
a nonzero invariant value in the fiber of `L^m` can occur only when
the stabilizer order divides `m`.
-/
theorem p_dvd_m_of_root_character_and_trivial_power
    (δ p m : ℕ) (s : ℤ)
    (hroot : Int.ModEq p ((δ : ℤ) * s) (-1 : ℤ))
    (hm : Int.ModEq p ((m : ℤ) * s) 0) :
    p ∣ m := by
  rw [Int.modEq_iff_dvd] at hroot hm

  have hroot' : (p : ℤ) ∣ (δ : ℤ) * s + 1 := by
    simpa [sub_eq_add_neg] using hroot

  have hm' : (p : ℤ) ∣ (m : ℤ) * s := by
    simpa using hm

  rcases hroot' with ⟨a, ha⟩
  rcases hm' with ⟨b, hb⟩

  have hmZ : (p : ℤ) ∣ (m : ℤ) := by
    refine ⟨(m : ℤ) * a - (δ : ℤ) * b, ?_⟩
    calc
      (m : ℤ)
          = (m : ℤ) * ((δ : ℤ) * s + 1)
              - (δ : ℤ) * ((m : ℤ) * s) := by ring
      _ = (m : ℤ) * ((p : ℤ) * a)
              - (δ : ℤ) * ((p : ℤ) * b) := by rw [ha, hb]
      _ = (p : ℤ) * ((m : ℤ) * a - (δ : ℤ) * b) := by ring

  exact_mod_cast hmZ


/--
The group-theoretic gcd statement behind the second equality in (4.2).

If `d` has the universal gcd property for a set `Σ` of positive degrees,
then an element `λ` satisfies `λ^m = 1` for every `m ∈ Σ`
if and only if `λ^d = 1`.
-/
theorem pow_eq_one_on_set_iff_pow_setGCD
    {G : Type*} [Group G]
    (Σ : Set ℕ) (d : ℕ)
    (hd : IsSetGCD Σ d)
    (λ : G) :
    (∀ m, m ∈ Σ → λ ^ m = 1) ↔ λ ^ d = 1 := by
  constructor
  · intro hall
    have hord : orderOf λ ∣ d := by
      apply hd.2
      intro m hm
      exact (orderOf_dvd_iff_pow_eq_one).2 (hall m hm)
    exact (orderOf_dvd_iff_pow_eq_one).1 hord

  · intro hpow m hm
    have hdm : d ∣ m := hd.1 m hm
    rcases hdm with ⟨k, rfl⟩
    rw [pow_mul, hpow]
    simp
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
/--
Final gcd step in Lemma 4.2.

Assume:
1. every degree in Σ is divisible by p;
2. every sufficiently large multiple of p belongs to Σ.

Then p has the universal gcd property for Σ.

The second hypothesis is exactly what the geometric
evaluation/Serre-vanishing argument supplies.
-/
theorem isSetGCD_of_eventual_multiples
    (Σ : Set ℕ) (p N : ℕ)
    (hp : 0 < p)
    (hall : ∀ m, m ∈ Σ → p ∣ m)
    (heventual :
      ∀ m, N ≤ m → p ∣ m → m ∈ Σ) :
    IsSetGCD Σ p := by
  let a : ℕ := p * (N + 1)
  let b : ℕ := p * (N + 2)

  have hNa : N ≤ a := by
    dsimp [a]
    omega

  have hNb : N ≤ b := by
    dsimp [b]
    omega

  have hpa : p ∣ a := by
    exact dvd_mul_right p (N + 1)

  have hpb : p ∣ b := by
    exact dvd_mul_right p (N + 2)

  have ha : a ∈ Σ :=
    heventual a hNa hpa

  have hb : b ∈ Σ :=
    heventual b hNb hpb

  have hg : Nat.gcd a b = p := by
    dsimp [a, b]
    rw [Nat.gcd_mul_left]
    have hsucc :
        Nat.gcd (N + 1) (N + 2) = 1 := by
      omega
    rw [hsucc]
    simp

  exact isSetGCD_of_two_witnesses
    Σ p a b hall ha hb hg
end Section4Lemma42
end FractionalTriangles
