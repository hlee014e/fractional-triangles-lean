import Mathlib
import FractionalTriangles.Grading
import FractionalTriangles.ScaledDegree

namespace FractionalTriangles

/-
We now descend the scaled degree map from Z^4 to the quotient grading group L.
This is the formal version of the paper's degree map after multiplication by N.
-/

def scaledDegree
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    GradingGroup p q r →+ ℤ :=
  QuotientAddGroup.lift
    (Relations p q r)
    (scaledDegreeAmbient p q r N)
    (relations_le_scaledDegree_kernel p q r N hp hq hr)

/-- The scaled degree of c is N. -/
theorem scaledDegree_c
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    scaledDegree p q r N hp hq hr (cbar p q r) = N := by
  rfl

/-- The scaled degree of x is N/p. -/
theorem scaledDegree_x
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    scaledDegree p q r N hp hq hr (xbar p q r) = N / p := by
  rfl

/-- The scaled degree of y is N/q. -/
theorem scaledDegree_y
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    scaledDegree p q r N hp hq hr (ybar p q r) = N / q := by
  rfl

/-- The scaled degree of z is N/r. -/
theorem scaledDegree_z
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    scaledDegree p q r N hp hq hr (zbar p q r) = N / r := by
  rfl

/-
Equation (2.2) in the paper says N*v = N*deg(v)*c.
For our integral scaled degree D(v)=N*deg(v), this becomes

    N • v = D(v) • c.

We first prove it on the four generators and then extend by quotient induction.
-/

theorem eq22_x
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    N • xbar p q r =
      (scaledDegree p q r N hp hq hr (xbar p q r)) • cbar p q r := by
  rw [scaledDegree_x]
  rcases hp with ⟨m, rfl⟩
  simp [Nat.mul_smul, p_x_eq_c]

theorem eq22_y
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    N • ybar p q r =
      (scaledDegree p q r N hp hq hr (ybar p q r)) • cbar p q r := by
  rw [scaledDegree_y]
  rcases hq with ⟨m, rfl⟩
  simp [Nat.mul_smul, q_y_eq_c]

theorem eq22_z
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    N • zbar p q r =
      (scaledDegree p q r N hp hq hr (zbar p q r)) • cbar p q r := by
  rw [scaledDegree_z]
  rcases hr with ⟨m, rfl⟩
  simp [Nat.mul_smul, r_z_eq_c]

theorem eq22_c
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    N • cbar p q r =
      (scaledDegree p q r N hp hq hr (cbar p q r)) • cbar p q r := by
  rw [scaledDegree_c]

end FractionalTriangles
