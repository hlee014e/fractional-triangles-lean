import Mathlib
import FractionalTriangles.Grading
import FractionalTriangles.ScaledDegree
import FractionalTriangles.Eq22
import FractionalTriangles.Eq22All
import FractionalTriangles.TorsionStep

namespace FractionalTriangles

/--
Concrete version of Lemma 2.1 for the grading group L(p,q,r).

Assume p,q,r divide N (as they do for N = lcm(p,q,r)).
If e > 0 and gcd(e,N)=1, then multiplication by e on L is injective.
-/
theorem lemma21_mul_injective
    (p q r N e : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (hepos : 0 < e)
    (hcop : Nat.Coprime e N) :
    Function.Injective (fun v : GradingGroup p q r => e • v) := by
  intro v w hvw
  let u : GradingGroup p q r := v - w
  have heu : e • u = 0 := by
    dsimp [u]
    rw [smul_sub, hvw, sub_self]

  have hdeg_eu :
      scaledDegree p q r N hp hq hr (e • u) = 0 := by
    rw [heu]
    simp

  have hdeg_mul :
      (e : ℤ) * scaledDegree p q r N hp hq hr u = 0 := by
    simpa using hdeg_eu

  have heZ : (e : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hepos)

  have hdeg_u :
      scaledDegree p q r N hp hq hr u = 0 := by
    exact (mul_eq_zero.mp hdeg_mul).resolve_left heZ

  have hNu : N • u = 0 :=
    killed_by_N_of_scaledDegree_zero p q r N hp hq hr u hdeg_u

  have hu : u = 0 :=
    eq_zero_of_coprime_annihilators e N hcop u heu hNu

  dsimp [u] at hu
  exact sub_eq_zero.mp hu

end FractionalTriangles
