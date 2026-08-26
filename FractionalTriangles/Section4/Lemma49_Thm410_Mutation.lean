import Mathlib
import FractionalTriangles.Section4.Lemma48_Table2_Eq413

namespace FractionalTriangles
namespace Section4

/-!
# Section 4 — Lemma 4.9 and the arithmetic spine of Theorem 4.10
Paper pp. 13–17.

This bundle checks the explicit integer arithmetic in the primitive atomic
mutation argument and several logical/numerical steps of Theorem 4.10.

No `sorry`, no axioms.
-/

/-! ## Lemma 4.9: equation (4.14) and case arithmetic -/

theorem fff_two_active_forces_two
    (q a : ℕ)
    (hq : 1 < q) (ha : 2 ≤ a)
    (heq : q*(a-1) = a) :
    q = 2 ∧ a = 2 := by
  omega

theorem fff_one_active_forces_three
    (q a b : ℕ)
    (hq : 1 < q)
    (ha : 3 ≤ a) (hb : 3 ≤ b)
    (h3q : 3 ∣ q)
    (heq : q*(a*b-a-b) = a*b) :
    q = 3 ∧ a = 3 ∧ b = 3 := by
  rcases h3q with ⟨k, rfl⟩
  omega

theorem c2f_case_419_forces_two
    (q a : ℕ)
    (hq : 1 < q) (ha : 2 ≤ a)
    (heq : q*(a-1)=a) :
    q=2 ∧ a=2 := by
  omega

theorem c2f_case_420_forces_two
    (q c : ℕ)
    (hq : 1 < q) (hc : 2 ≤ c)
    (heq : q*(c-1)=c) :
    q=2 ∧ c=2 := by
  omega

theorem ec_minus_one_eq_two
    (e c : ℕ)
    (he : 1 ≤ e) (hc : 2 ≤ c)
    (h : e*(c-1)=2) :
    (e=1 ∧ c=3) ∨ (e=2 ∧ c=2) := by
  omega

/-! ## Theorem 4.10: paper-specific elementary steps -/

theorem mixed_quadratic_contradiction
    (A B C h : ℤ)
    (hC : 0 < C)
    (hxy : A+B=h)
    (hpos : 0 < h-A-B-C) :
    False := by
  rw [← hxy] at hpos
  linarith

theorem weighted_euler_at_critical
    {K : Type*} [Field K]
    (h A B C F x y z Fx Fy Fz : K)
    (heuler : h*F = A*x*Fx + B*y*Fy + C*z*Fz)
    (hx : Fx=0) (hy : Fy=0) (hz : Fz=0) :
    h*F=0 := by
  rw [hx,hy,hz] at heuler
  simpa using heuler

theorem weighted_euler_critical_on_hypersurface
    {K : Type*} [Field K]
    (h F : K) (hh : h ≠ 0)
    (hprod : h*F=0) :
    F=0 := by
  exact (mul_eq_zero.mp hprod).resolve_left hh

end Section4
end FractionalTriangles
