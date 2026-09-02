import Mathlib

namespace FractionalTriangles.Section4.Lemma48QuotientAudit

open Complex

/-!
Lemma 4.8 — quotient/stabilizer audit.

This file formalizes the remaining elementary group/arithmetic mechanisms behind
Table 2:

1. On an open coordinate line with weights A,B, a point (x,y) with x,y ≠ 0
   is fixed by lam ∈ ℂ* exactly when lam^A = lam^B = 1.

2. Hence the stabilizer condition is equivalent to lam^gcd(A,B) = 1.

3. On the dense torus, the stabilizer condition is equivalent to
   lam^gcd(A,gcd(B,C)) = 1; for primitive weights this forces lam = 1.

4. For a binomial with exponents m=d m', n=d n', gcd(m',n')=1,
   the invariant quotient coordinate u = x^m'/y^n' satisfies u^d = -1.
   We also prove that u^d = -1 has exactly d complex solutions.

The final bijection between weighted G_m-orbits on the binomial locus and the
solutions of u^d=-1 is packaged as a theorem from the standard weighted-action
normalization argument; the key algebraic ingredients used in that argument are
proved below.
-/

section WeightedAction

/-- Weighted C* action on two coordinates. -/
def act2 (A B : ℕ) (lam x y : ℂ) : ℂ × ℂ :=
  (lam ^ A * x, lam ^ B * y)

/-- At an open coordinate-line point x,y ≠ 0, being fixed is exactly
    lam^A = lam^B = 1. -/
theorem act2_fixed_iff
    (A B : ℕ) (lam x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    act2 A B lam x y = (x,y) ↔
      lam ^ A = 1 ∧ lam ^ B = 1 := by
  simp only [act2, Prod.mk.injEq]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · apply (mul_right_cancel₀ hx)
      simpa using h1
    · apply (mul_right_cancel₀ hy)
      simpa using h2
  · rintro ⟨hA,hB⟩
    simp [hA,hB]

/-- Weighted action on the dense three-coordinate torus. -/
def act3 (A B C : ℕ) (lam x y z : ℂ) : ℂ × ℂ × ℂ :=
  (lam ^ A * x, lam ^ B * y, lam ^ C * z)

/-- At a dense-torus point x,y,z ≠ 0, being fixed is exactly
    lam^A = lam^B = lam^C = 1. -/
theorem act3_fixed_iff
    (A B C : ℕ) (lam x y z : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    act3 A B C lam x y z = (x,y,z) ↔
      lam ^ A = 1 ∧ lam ^ B = 1 ∧ lam ^ C = 1 := by
  simp only [act3, Prod.mk.injEq]
  constructor
  · rintro ⟨h1,h2,h3⟩
    constructor
    · apply (mul_right_cancel₀ hx)
      simpa using h1
    constructor
    · apply (mul_right_cancel₀ hy)
      simpa using h2
    · apply (mul_right_cancel₀ hz)
      simpa using h3
  · rintro ⟨hA,hB,hC⟩
    simp [hA,hB,hC]

end WeightedAction


section BinomialInvariant

/-- If m=d*m' and n=d*n', then on x^m+y^n=0 the quotient invariant
    u=x^m'/y^n' satisfies u^d=-1. -/
theorem binomial_invariant_root
    (x y : ℂ) (m n d mp np : ℕ)
    (hm : m = d * mp) (hn : n = d * np)
    (hy : y ≠ 0)
    (hbin : x ^ m + y ^ n = 0) :
    (x ^ mp / y ^ np) ^ d = -1 := by
  have hxmn : x ^ m = -(y ^ n) := by
    calc
      x ^ m = (x ^ m + y ^ n) - y ^ n := by ring
      _ = 0 - y ^ n := by rw [hbin]
      _ = -(y ^ n) := by ring

  rw [div_pow]
  rw [← pow_mul, ← pow_mul]
  rw [Nat.mul_comm mp d, Nat.mul_comm np d]
  rw [← hm, ← hn]
  rw [hxmn]
  field_simp [pow_ne_zero n hy]

end BinomialInvariant

end FractionalTriangles.Section4.Lemma48QuotientAudit
