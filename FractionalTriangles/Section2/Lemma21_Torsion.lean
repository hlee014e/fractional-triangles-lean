import Mathlib
import FractionalTriangles.Section2.GradingGroup
import FractionalTriangles.Section2.ScaledDegree
import FractionalTriangles.Section2.Equation22_Generators

namespace FractionalTriangles

/-
Next Section 2 step:
from equation (2.2), any element in the kernel of the degree map is killed by N.
This is the key fact used to prove Lemma 2.1.
-/

variable {p q r N : ℕ}
variable (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)

/-- If the scaled degree of v is zero, then N • v = 0.
This is equation (2.2) specialized to degree-zero elements. -/
theorem nsmul_eq_zero_of_scaledDegree_eq_zero
    (v : GradingGroup p q r)
    (hdeg : scaledDegree p q r N hp hq hr v = 0)
    (heq22 :
      N • v =
        (scaledDegree p q r N hp hq hr v) • cbar p q r) :
    N • v = 0 := by
  rw [heq22, hdeg]
  simp

/-- Bézout step behind Lemma 2.1:
if e and N are coprime, and both e and N kill v, then v = 0. -/
theorem eq_zero_of_coprime_annihilators
    {L : Type*} [AddCommGroup L]
    (e N : ℕ) (hcop : Nat.Coprime e N)
    (v : L)
    (he : e • v = 0)
    (hN : N • v = 0) :
    v = 0 := by
  rcases hcop with ⟨a, b, hab⟩
  have hbez : (a : ℤ) * e + (b : ℤ) * N = 1 := by
    exact_mod_cast hab
  calc
    v = (1 : ℤ) • v := by simp
    _ = (((a : ℤ) * e + (b : ℤ) * N) : ℤ) • v := by rw [hbez]
    _ = ((a : ℤ) * e) • v + ((b : ℤ) * N) • v := by
      rw [add_smul]
    _ = (a : ℤ) • (e • v) + (b : ℤ) • (N • v) := by
      simp [smul_smul]
    _ = 0 := by simp [he, hN]

/-- Abstract Lemma 2.1 mechanism:
if every degree-zero element is killed by N, then multiplication by e is injective
for gcd(e,N)=1. -/
theorem mul_injective_of_coprime
    {L : Type*} [AddCommGroup L]
    (e N : ℕ)
    (hcop : Nat.Coprime e N)
    (hNkernel : ∀ v : L, e • v = 0 → N • v = 0) :
    Function.Injective (fun v : L => e • v) := by
  intro v w hvw
  have hkill : e • (v - w) = 0 := by
    rw [smul_sub, hvw, sub_self]
  have hNkill : N • (v - w) = 0 := hNkernel (v - w) hkill
  have hz : v - w = 0 :=
    eq_zero_of_coprime_annihilators e N hcop (v - w) hkill hNkill
  exact sub_eq_zero.mp hz

end FractionalTriangles
