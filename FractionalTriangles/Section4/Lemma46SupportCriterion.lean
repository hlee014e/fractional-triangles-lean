import Mathlib

namespace FractionalTriangles
namespace Section4

/-!
# Lemma 4.6 — support criterion

We formalize the nontrivial finite-combinatorial step used in
Lemma 4.6.

External input:
Rarovskii [19, Theorem 8], which relates nondegeneracy to the
support conditions (C1)–(C2)'.

The point formalized here is the argument for the branched rows:
for J = {x,z}, condition (C1) forces the support to contain a
monomial involving only x and z.
-/

/-- The three variables. -/
inductive Var
  | x | y | z
  deriving DecidableEq, Repr

/-- A monomial is represented by its exponent vector. -/
abbrev Monomial := Var → ℕ

/-- The full variable set I = {x,y,z}. -/
def allVars : Finset Var :=
  {Var.x, Var.y, Var.z}

/-- `SupportedIn α J` means that α uses only variables in J. -/
def SupportedIn (α : Monomial) (J : Finset Var) : Prop :=
  ∀ v, α v ≠ 0 → v ∈ J

/-- α + e_k. -/
def addVar (α : Monomial) (k : Var) : Monomial :=
  fun v => α v + if v = k then 1 else 0

/-- R_k in the notation of the support criterion. -/
def Rk (R : Set Monomial) (k : Var) : Set Monomial :=
  {α | addVar α k ∈ R}

/-- First alternative in condition (C1). -/
def C1First (R : Set Monomial) (J : Finset Var) : Prop :=
  ∃ α ∈ R, SupportedIn α J

/-- Second alternative in condition (C1). -/
def C1Second (R : Set Monomial) (J : Finset Var) : Prop :=
  ∃ K : Finset Var,
    K ⊆ allVars \ J ∧
    K.card = J.card ∧
    ∀ k ∈ K, ∃ α ∈ Rk R k, SupportedIn α J

/-- Rarovskii's condition (C1), in the form used here. -/
def C1 (R : Set Monomial) (J : Finset Var) : Prop :=
  C1First R J ∨ C1Second R J

/-- The subset J={x,z}. -/
def xz : Finset Var :=
  {Var.x, Var.z}

/--
For J={x,z}, the second alternative of (C1) is impossible:
I\J={y} has one element, whereas |J|=2.
-/
theorem c1Second_xz_impossible
    (R : Set Monomial) :
    ¬ C1Second R xz := by
  intro h
  obtain ⟨K, hK, hcard, _⟩ := h

  have hcomp : allVars \ xz = {Var.y} := by
    ext v
    cases v <;> simp [allVars, xz]

  have hK' : K ⊆ ({Var.y} : Finset Var) := by
    rw [← hcomp]
    exact hK

  have hle : K.card ≤ 1 := by
    have h := Finset.card_le_card hK'
    simpa using h

  have hcard_two : K.card = 2 := by
    have hxz : xz.card = 2 := by
      simp [xz]
    calc
      K.card = xz.card := hcard
      _ = 2 := hxz

  omega

/--
Hence (C1) for J={x,z} must use its first alternative.
-/
theorem c1_xz_forces_first
    (R : Set Monomial)
    (hC1 : C1 R xz) :
    C1First R xz := by
  rcases hC1 with hfirst | hsecond
  · exact hfirst
  · exact False.elim (c1Second_xz_impossible R hsecond)

/--
A monomial supported in {x,z} has zero y-exponent.
-/
theorem supportedIn_xz_y_zero
    (α : Monomial)
    (hα : SupportedIn α xz) :
    α Var.y = 0 := by
  by_contra hy
  have hy_mem : Var.y ∈ xz := hα Var.y hy
  simp [xz] at hy_mem

/--
Main combinatorial consequence used in Lemma 4.6:

(C1) for J={x,z} forces a monomial x^m z^n in the support.
-/
theorem branched_support_has_xz_monomial
    (R : Set Monomial)
    (hC1 : C1 R xz) :
    ∃ α ∈ R, α Var.y = 0 := by
  have hfirst := c1_xz_forces_first R hC1
  obtain ⟨α, hαR, hαxz⟩ := hfirst
  exact ⟨α, hαR, supportedIn_xz_y_zero α hαxz⟩

/--
For x^m z^n there are exactly the two cases used in the paper:
a pure power, or a genuine positive x-z link.
-/
theorem xz_monomial_pure_or_positive_link
    (m n : ℕ) :
    m = 0 ∨ n = 0 ∨ (0 < m ∧ 0 < n) := by
  omega

/-!
Thus the Lean-verified part of the last paragraph of Lemma 4.6 is

  (C1), J={x,z}
      => some x^m z^n occurs,

and then

  m=0 or n=0        => pure-power case,
  m>0 and n>0       => genuine x-z link.

The classification of the seven ternary graphs and the implication
from nondegeneracy to (C1)–(C2)' remain external results from [19].
-/

end Section4
end FractionalTriangles
