import Mathlib
import FractionalTriangles.Section4_Lemma42
import FractionalTriangles.Section4_Lemma42Characters

namespace FractionalTriangles
namespace Section4Lemma42Fiber

/-!
# Lemma 4.2 — fiber-character and invariant-vector arithmetic

Paper: Lemma 4.2, pp. 7–8.

This file formalizes the elementary representation-theoretic consequences
used in the residual-gerbe evaluation argument.

Geometric input not formalized here:
  H^0(B μ_p, V) is the invariant subspace V^{μ_p}.
-/

/--
If the root character satisfies

    δ s ≡ -1 (mod p),

then the character of the m-th tensor power is trivial exactly when p divides m.
-/
theorem trivial_fiber_character_iff_dvd
    (δ p m : ℕ) (s : ℤ)
    (hroot : Int.ModEq p ((δ : ℤ) * s) (-1 : ℤ)) :
    Int.ModEq p ((m : ℤ) * s) 0 ↔ p ∣ m := by
  constructor

  · intro hm
    exact
      Section4Lemma42.p_dvd_m_of_root_character_and_trivial_power
        δ p m s hroot hm

  · intro hpm
    rw [Int.modEq_iff_dvd]
    have hpZ : (p : ℤ) ∣ (m : ℤ) := by
      exact_mod_cast hpm
    simpa using (dvd_mul_of_dvd_left hpZ s)


/--
Consequently, if p does not divide m, the character of L^m on the residual
gerbe is nontrivial.
-/
theorem nontrivial_fiber_character_of_not_dvd
    (δ p m : ℕ) (s : ℤ)
    (hroot : Int.ModEq p ((δ : ℤ) * s) (-1 : ℤ))
    (hm : ¬ p ∣ m) :
    ¬ Int.ModEq p ((m : ℤ) * s) 0 := by
  intro htriv
  exact hm ((trivial_fiber_character_iff_dvd δ p m s hroot).mp htriv)


/--
Elementary linear algebra behind

    H^0(B μ_p, V) = 0

for a nontrivial one-dimensional character.

If a scalar `a ≠ 1` acts on a one-dimensional vector `v`, and `v` is fixed,
then `v = 0`.
-/
theorem invariant_vector_eq_zero_of_nontrivial_scalar
    {K : Type*} [Field K]
    (a v : K)
    (ha : a ≠ 1)
    (hinv : a * v = v) :
    v = 0 := by
  have h : (a - 1) * v = 0 := by
    rw [sub_mul, one_mul, hinv, sub_self]
  exact
    (mul_eq_zero.mp h).resolve_left
      (sub_ne_zero.mpr ha)


/--
For the trivial character every vector is invariant.
-/
theorem invariant_vector_of_trivial_scalar
    {K : Type*} [Field K]
    (v : K) :
    (1 : K) * v = v := by
  simp


/--
Package the three root-character calculations already obtained from the
concrete grading group L(p,q,r).
-/
theorem three_root_characters
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (hroot : δ • τ = omega p q r) :
    δ • Section4Lemma42Characters.charX p q r τ = -1 ∧
    δ • Section4Lemma42Characters.charY p q r τ = -1 ∧
    δ • Section4Lemma42Characters.charZ p q r τ = -1 := by
  exact ⟨
    Section4Lemma42Characters.root_character_X p q r δ τ hroot,
    Section4Lemma42Characters.root_character_Y p q r δ τ hroot,
    Section4Lemma42Characters.root_character_Z p q r δ τ hroot
  ⟩

end Section4Lemma42Fiber
end FractionalTriangles
