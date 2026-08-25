import Mathlib
import FractionalTriangles.Section2.GradingGroup
import FractionalTriangles.Section2.ScaledDegree
import FractionalTriangles.Section2.Equation22_Generators
import FractionalTriangles.Section2.Lemma21_Torsion

namespace FractionalTriangles

/-
This file upgrades equation (2.2) from the four generators to every element of L.

Mathematically, both sides are additive in v:
  v ↦ N • v
and
  v ↦ (N deg v) • c.
So it is enough to verify equality on x,y,z,c, which was done in Eq22.lean.
We package both sides as additive homomorphisms and compare them on representatives
of Z^4.
-/

def nsmulHom (p q r N : ℕ) :
    GradingGroup p q r →+ GradingGroup p q r where
  toFun := fun v => N • v
  map_zero' := by simp
  map_add' := by
    intro a b
    simp [smul_add]

def degreeTimesCHom
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N) :
    GradingGroup p q r →+ GradingGroup p q r where
  toFun := fun v =>
    (scaledDegree p q r N hp hq hr v) • cbar p q r
  map_zero' := by simp
  map_add' := by
    intro a b
    simp [add_smul]

/-- Equation (2.2), in integral scaled-degree form, for every v ∈ L. -/
theorem eq22_all
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (v : GradingGroup p q r) :
    N • v =
      (scaledDegree p q r N hp hq hr v) • cbar p q r := by
  -- Reduce to a representative of Z^4.
  refine QuotientAddGroup.induction_on v ?_
  intro a
  -- Every vector in Z^4 is the sum of its four coordinate multiples.
  have ha :
      a =
        a 0 • (![1,0,0,0] : Ambient) +
        a 1 • (![0,1,0,0] : Ambient) +
        a 2 • (![0,0,1,0] : Ambient) +
        a 3 • (![0,0,0,1] : Ambient) := by
    funext i
    fin_cases i <;> simp
  rw [ha]
  simp only [map_add, map_zsmul]
  -- The four generator cases were proved in Eq22.lean.
  simp [nsmulHom, degreeTimesCHom,
        eq22_x p q r N hp hq hr,
        eq22_y p q r N hp hq hr,
        eq22_z p q r N hp hq hr,
        eq22_c p q r N hp hq hr,
        smul_add, add_smul, smul_smul]

/-- Concrete consequence of (2.2): scaled degree zero implies N-torsion. -/
theorem killed_by_N_of_scaledDegree_zero
    (p q r N : ℕ)
    (hp : p ∣ N) (hq : q ∣ N) (hr : r ∣ N)
    (v : GradingGroup p q r)
    (hdeg : scaledDegree p q r N hp hq hr v = 0) :
    N • v = 0 := by
  rw [eq22_all p q r N hp hq hr v, hdeg]
  simp

end FractionalTriangles
