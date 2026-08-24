import Mathlib
import FractionalTriangles.Grading

namespace FractionalTriangles

/-
This is the next compile-test toward Section 2.
Instead of introducing rational degree immediately, we first use the integral
scaled degree N*deg:
  x |-> N/p,  y |-> N/q,  z |-> N/r,  c |-> N.
The assumptions p|N, q|N, r|N are exactly what holds for N=lcm(p,q,r).
-/

def scaledDegreeAmbient (p q r N : ℕ) : Ambient →+ ℤ where
  toFun := fun v =>
    v 0 * (N / p : ℕ) + v 1 * (N / q : ℕ) +
    v 2 * (N / r : ℕ) + v 3 * (N : ℤ)
  map_zero' := by
    simp
  map_add' := by
    intro a b
    simp
    ring

theorem scaledDegreeAmbient_relX
    (p q r N : ℕ) (hp : p ∣ N) :
    scaledDegreeAmbient p q r N (relX p) = 0 := by
  rcases hp with ⟨m, rfl⟩
  simp [scaledDegreeAmbient, relX]
  ring

theorem scaledDegreeAmbient_relY
    (p q r N : ℕ) (hq : q ∣ N) :
    scaledDegreeAmbient p q r N (relY q) = 0 := by
  rcases hq with ⟨m, rfl⟩
  simp [scaledDegreeAmbient, relY]
  ring

theorem scaledDegreeAmbient_relZ
    (p q r N : ℕ) (hr : r ∣ N) :
    scaledDegreeAmbient p q r N (relZ r) = 0 := by
  rcases hr with ⟨m, rfl⟩
  simp [scaledDegreeAmbient, relZ]
  ring

/-- All defining relations lie in the kernel of the scaled-degree map. -/
theorem relations_le_scaledDegree_kernel
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    Relations p q r ≤ (scaledDegreeAmbient p q r N).ker := by
  apply AddSubgroup.closure_le.2
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h
  · subst v
    exact scaledDegreeAmbient_relX p q r N hp
  · subst v
    exact scaledDegreeAmbient_relY p q r N hq
  · subst v
    exact scaledDegreeAmbient_relZ p q r N hr

/-
The next theorem will descend `scaledDegreeAmbient` to `GradingGroup p q r`.
We keep that descent as the next tiny step so that any quotient-API mismatch
is isolated and easy to repair.
-/

end FractionalTriangles
