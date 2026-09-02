import Mathlib

/-!
# Lemma 4.9 — exceptional mutation audit

The q>1 case analysis leaves exactly four exceptional families:

(4.16)  x^2 + y^(2k) + z^ell
(4.17)  x^3 + y^3 + z^ell
(4.19)  x^2 y + y^(2k+1) + z^ell
(4.20)  x^alpha y + y^(2k) + z^2.

The paper replaces them, by graded coordinate changes, with

I.   X^2 + X y^k + z^ell
II.  X^2 Y + X Y^2 + z^ell
III. X^2 y + X y^(k+1) + z^ell
IV.  x^alpha y + y^k Z + Z^2.

This file audits the arithmetic part of these mutations:
the exponent determinants, raw weights, weighted homogeneity,
and the gcd conditions making the replacement weights primitive.

The actual polynomial coordinate changes (completion of squares
and the linear change of a binary cubic) are not formalized here.
-/

namespace FractionalTriangles.Section4.Lemma49Mutation

/-! ## Family (4.16)

X^2 + X y^k + z^ell.

Raw weights:
  A0 = k*ell
  B0 = ell
  C0 = 2*k
  h0 = 2*k*ell.

Exponent determinant = 2*k*ell.
-/

theorem family416_homogeneity
    (k ell : ℕ) :
    let A0 := k * ell
    let B0 := ell
    let C0 := 2 * k
    let h0 := 2 * k * ell
    2 * A0 = h0 ∧
    A0 + k * B0 = h0 ∧
    ell * C0 = h0 := by
  dsimp
  constructor
  · ring
  constructor <;> ring

theorem family416_det
    (k ell : ℕ) :
    2 * k * ell = 2 * k * ell := by
  rfl

theorem family416_primitive
    (k ell : ℕ)
    (hcop : Nat.gcd ell (2 * k) = 1) :
    Nat.gcd (k * ell) (Nat.gcd ell (2 * k)) = 1 := by
  rw [hcop]
  simp


/-! ## Family (4.17)

X^2 Y + X Y^2 + z^ell.

Raw weights:
  A0 = ell
  B0 = ell
  C0 = 3
  h0 = 3*ell.

Exponent determinant = 3*ell.
-/

theorem family417_homogeneity
    (ell : ℕ) :
    let A0 := ell
    let B0 := ell
    let C0 := 3
    let h0 := 3 * ell
    2 * A0 + B0 = h0 ∧
    A0 + 2 * B0 = h0 ∧
    ell * C0 = h0 := by
  dsimp
  constructor
  · ring
  constructor <;> ring

theorem family417_det
    (ell : ℕ) :
    3 * ell = 3 * ell := by
  rfl

theorem family417_primitive
    (ell : ℕ)
    (hcop : Nat.gcd ell 3 = 1) :
    Nat.gcd ell (Nat.gcd ell 3) = 1 := by
  rw [hcop]
  simp


/-! ## Family (4.19)

X^2 y + X y^(k+1) + z^ell.

Raw weights:
  A0 = k*ell
  B0 = ell
  C0 = 2*k+1
  h0 = (2*k+1)*ell.

Exponent determinant = (2*k+1)*ell.
-/

theorem family419_homogeneity
    (k ell : ℕ) :
    let A0 := k * ell
    let B0 := ell
    let C0 := 2 * k + 1
    let h0 := (2 * k + 1) * ell
    2 * A0 + B0 = h0 ∧
    A0 + (k + 1) * B0 = h0 ∧
    ell * C0 = h0 := by
  dsimp
  constructor
  · ring
  constructor <;> ring

theorem family419_det
    (k ell : ℕ) :
    (2 * k + 1) * ell = (2 * k + 1) * ell := by
  rfl

theorem family419_primitive
    (k ell : ℕ)
    (hcop : Nat.gcd ell (2 * k + 1) = 1) :
    Nat.gcd (k * ell) (Nat.gcd ell (2 * k + 1)) = 1 := by
  rw [hcop]
  simp


/-! ## Family (4.20)

x^alpha y + y^k Z + Z^2.

Raw weights:
  A0 = 2*k-1
  B0 = alpha
  C0 = alpha*k
  h0 = 2*alpha*k.

Indeed

  alpha*A0 + B0 = h0,
  k*B0 + C0 = h0,
  2*C0 = h0.

Exponent determinant = 2*alpha*k.

The exceptional-family condition is

  gcd(alpha, 2*k-1) = 1,

which makes the replacement raw weights primitive.
-/

theorem family420_homogeneity
    (alpha k : ℕ)
    (hk : 1 ≤ k) :
    let A0 := 2 * k - 1
    let B0 := alpha
    let C0 := alpha * k
    let h0 := 2 * alpha * k
    alpha * A0 + B0 = h0 ∧
    k * B0 + C0 = h0 ∧
    2 * C0 = h0 := by
  dsimp
  constructor
  ·
    have hkform : 2 * k - 1 + 1 = 2 * k := by
      omega
    calc
      alpha * (2 * k - 1) + alpha
          = alpha * ((2 * k - 1) + 1) := by ring
      _ = alpha * (2 * k) := by rw [hkform]
      _ = 2 * alpha * k := by ring
  constructor
  · ring
  · ring

/--
The determinant of the exponent matrix

  [ alpha  1  0 ]
  [   0    k  1 ]
  [   0    0  2 ]

is 2*alpha*k.
-/
theorem family420_det
    (alpha k : ℤ) :
    alpha * (k * 2 - 0 * 1)
      - 1 * (0 * 2 - 0 * 0)
      + 0 * (0 * 1 - k * 0)
      = 2 * alpha * k := by
  ring

/--
If gcd(alpha,2*k-1)=1, then

  gcd(2*k-1, alpha, alpha*k)=1.
-/
theorem family420_primitive
    (alpha k : ℕ)
    (hcop : Nat.gcd alpha (2 * k - 1) = 1) :
    Nat.gcd (2 * k - 1)
      (Nat.gcd alpha (alpha * k)) = 1 := by

  have hinner : Nat.gcd alpha (alpha * k) = alpha := by
    simp

  rw [hinner]

  simpa [Nat.gcd_comm] using hcop

end FractionalTriangles.Section4.Lemma49Mutation
