import Mathlib
import FractionalTriangles.Section2.GradingGroup
import FractionalTriangles.Section4.Lemma42_Reconstruction

namespace FractionalTriangles
namespace Section4Lemma42Characters

/-
At the p-stacky point P₁, restriction of O_X(v) to the residual gerbe
B μ_p has a character in Z/pZ.

On the concrete grading group this is the homomorphism
  x ↦ 1,  y ↦ 0,  z ↦ 0,  c ↦ 0.
-/

def ambientCharX (p : ℕ) : Ambient →+ ZMod p where
  toFun v := (v 0 : ZMod p)
  map_zero' := by simp
  map_add' := by
    intro a b
    simp

theorem relations_le_ker_ambientCharX
    (p q r : ℕ) :
    Relations p q r ≤ (ambientCharX p).ker := by
  apply AddSubgroup.closure_le.2
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h
  · subst v
    simp [ambientCharX, relX]
  · subst v
    simp [ambientCharX, relY]
  · subst v
    simp [ambientCharX, relZ]

def charX (p q r : ℕ) :
    GradingGroup p q r →+ ZMod p :=
  QuotientAddGroup.lift (Relations p q r) (ambientCharX p)
    (relations_le_ker_ambientCharX p q r)

theorem charX_x (p q r : ℕ) :
    charX p q r (xbar p q r) = 1 := by
  rfl

theorem charX_y (p q r : ℕ) :
    charX p q r (ybar p q r) = 0 := by
  rfl

theorem charX_z (p q r : ℕ) :
    charX p q r (zbar p q r) = 0 := by
  rfl

theorem charX_c (p q r : ℕ) :
    charX p q r (cbar p q r) = 0 := by
  rfl

/--
At the p-stacky point, ω = c-x-y-z has character -1.
-/
theorem charX_omega (p q r : ℕ) :
    charX p q r (omega p q r) = -1 := by
  simp [omega, charX_x, charX_y, charX_z, charX_c]

/--
If δ τ = ω in L(p,q,r), and s is the character of τ at P₁,
then δ s = -1 in Z/pZ.
-/
theorem root_character_X
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (hroot : δ • τ = omega p q r) :
    δ • charX p q r τ = -1 := by
  rw [← map_nsmul, hroot, charX_omega]
/-
At the q-stacky point P₂:
  x ↦ 0, y ↦ 1, z ↦ 0, c ↦ 0.
-/

def ambientCharY (q : ℕ) : Ambient →+ ZMod q where
  toFun v := (v 1 : ZMod q)
  map_zero' := by simp
  map_add' := by
    intro a b
    simp

theorem relations_le_ker_ambientCharY
    (p q r : ℕ) :
    Relations p q r ≤ (ambientCharY q).ker := by
  apply AddSubgroup.closure_le.2
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h
  · subst v
    simp [ambientCharY, relX]
  · subst v
    simp [ambientCharY, relY]
  · subst v
    simp [ambientCharY, relZ]

def charY (p q r : ℕ) :
    GradingGroup p q r →+ ZMod q :=
  QuotientAddGroup.lift (Relations p q r) (ambientCharY q)
    (relations_le_ker_ambientCharY p q r)

@[simp] theorem charY_x (p q r : ℕ) :
    charY p q r (xbar p q r) = 0 := by
  rfl

@[simp] theorem charY_y (p q r : ℕ) :
    charY p q r (ybar p q r) = 1 := by
  rfl

@[simp] theorem charY_z (p q r : ℕ) :
    charY p q r (zbar p q r) = 0 := by
  rfl

@[simp] theorem charY_c (p q r : ℕ) :
    charY p q r (cbar p q r) = 0 := by
  rfl

theorem charY_omega (p q r : ℕ) :
    charY p q r (omega p q r) = -1 := by
  simp [omega]

theorem root_character_Y
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (hroot : δ • τ = omega p q r) :
    δ • charY p q r τ = -1 := by
  rw [← map_nsmul, hroot, charY_omega]


/-
At the r-stacky point P₃:
  x ↦ 0, y ↦ 0, z ↦ 1, c ↦ 0.
-/

def ambientCharZ (r : ℕ) : Ambient →+ ZMod r where
  toFun v := (v 2 : ZMod r)
  map_zero' := by simp
  map_add' := by
    intro a b
    simp

theorem relations_le_ker_ambientCharZ
    (p q r : ℕ) :
    Relations p q r ≤ (ambientCharZ r).ker := by
  apply AddSubgroup.closure_le.2
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h
  · subst v
    simp [ambientCharZ, relX]
  · subst v
    simp [ambientCharZ, relY]
  · subst v
    simp [ambientCharZ, relZ]

def charZ (p q r : ℕ) :
    GradingGroup p q r →+ ZMod r :=
  QuotientAddGroup.lift (Relations p q r) (ambientCharZ r)
    (relations_le_ker_ambientCharZ p q r)

@[simp] theorem charZ_x (p q r : ℕ) :
    charZ p q r (xbar p q r) = 0 := by
  rfl

@[simp] theorem charZ_y (p q r : ℕ) :
    charZ p q r (ybar p q r) = 0 := by
  rfl

@[simp] theorem charZ_z (p q r : ℕ) :
    charZ p q r (zbar p q r) = 1 := by
  rfl

@[simp] theorem charZ_c (p q r : ℕ) :
    charZ p q r (cbar p q r) = 0 := by
  rfl

theorem charZ_omega (p q r : ℕ) :
    charZ p q r (omega p q r) = -1 := by
  simp [omega]

theorem root_character_Z
    (p q r δ : ℕ)
    (τ : GradingGroup p q r)
    (hroot : δ • τ = omega p q r) :
    δ • charZ p q r τ = -1 := by
  rw [← map_nsmul, hroot, charZ_omega]
end Section4Lemma42Characters
end FractionalTriangles
