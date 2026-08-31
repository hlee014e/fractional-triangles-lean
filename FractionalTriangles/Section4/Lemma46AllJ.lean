import FractionalTriangles.Section4.Lemma46SupportCriterion

namespace FractionalTriangles
namespace Section4

/-!
# Lemma 4.6 — all relevant J

This file completes the finite support checks for the two branched
supports appearing in Lemma 4.6.

The external input [19, Theorem 8] is NOT formalized here.
We only verify the finite (C1)–(C2)' support conditions.
-/

/-- The (C2)' condition used in the support check. -/
def C2 (R : Set Monomial) (J : Finset Var) : Prop :=
  ∃ K : Finset Var,
    K ⊆ allVars ∧
    K.card = J.card ∧
    ∀ k ∈ K, ∃ α ∈ Rk R k, SupportedIn α J

def singletonX : Finset Var := {Var.x}
def singletonY : Finset Var := {Var.y}
def singletonZ : Finset Var := {Var.z}
def xy : Finset Var := {Var.x, Var.y}
def yz : Finset Var := {Var.y, Var.z}

/-- All nonempty proper subsets J ⊂ {x,y,z}. -/
def relevantJs : Finset (Finset Var) :=
  [singletonX, singletonY, singletonZ, xy, xz, yz].toFinset

/-- Remove one copy of variable k from a monomial. -/
def removeVar (β : Monomial) (k : Var) : Monomial :=
  fun v => if v = k then β v - 1 else β v

theorem addVar_removeVar
    (β : Monomial) (k : Var)
    (hk : 0 < β k) :
    addVar (removeVar β k) k = β := by
  funext v
  by_cases hv : v = k
  · subst v
    have hk1 : β k - 1 + 1 = β k := by
      omega
    simp [addVar, removeVar, hk1]
  · simp [addVar, removeVar, hv]

/-- A monomial β∈R with positive k-exponent gives the derivative witness β-e_k ∈ R_k. -/
theorem derivativeWitness
    (R : Set Monomial)
    (β : Monomial)
    (k : Var)
    (J : Finset Var)
    (hβ : β ∈ R)
    (hk : 0 < β k)
    (hsupp : SupportedIn (removeVar β k) J) :
    ∃ α ∈ Rk R k, SupportedIn α J := by
  refine ⟨removeVar β k, ?_, hsupp⟩
  change addVar (removeVar β k) k ∈ R
  rw [addVar_removeVar β k hk]
  exact hβ

/-! Monomials used in rows 3 and 6. -/

def mon_xay (a : ℕ) : Monomial
  | Var.x => a
  | Var.y => 1
  | Var.z => 0

def mon_zcy (c : ℕ) : Monomial
  | Var.x => 0
  | Var.y => 1
  | Var.z => c

def mon_yb (b : ℕ) : Monomial
  | Var.x => 0
  | Var.y => b
  | Var.z => 0

def mon_ybz (b : ℕ) : Monomial
  | Var.x => 0
  | Var.y => b
  | Var.z => 1

def mon_xmzn (m n : ℕ) : Monomial
  | Var.x => m
  | Var.y => 0
  | Var.z => n

def R3 (a b c m n : ℕ) : Set Monomial :=
  {α |
    α = mon_xay a ∨
    α = mon_zcy c ∨
    α = mon_yb b ∨
    α = mon_xmzn m n}

def R6 (a b c m n : ℕ) : Set Monomial :=
  {α |
    α = mon_xay a ∨
    α = mon_ybz b ∨
    α = mon_zcy c ∨
    α = mon_xmzn m n}

/-!
Row 3:
  R3 = {x^a y, z^c y, y^b, x^m z^n}.
-/
theorem R3_all_support_conditions
    (a b c m n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hm : 0 < m) (hn : 0 < n) :
    ∀ J ∈ relevantJs, C1 (R3 a b c m n) J ∧ C2 (R3 a b c m n) J := by

  let R := R3 a b c m n

  have wx :
      ∃ α ∈ Rk R Var.y, SupportedIn α singletonX := by
    apply derivativeWitness R (mon_xay a) Var.y singletonX
    · simp [R, R3]
    · simp [mon_xay]
    · intro v hv
      cases v <;> simp [removeVar, mon_xay, singletonX] at *

  have wy :
      ∃ α ∈ Rk R Var.y, SupportedIn α singletonY := by
    apply derivativeWitness R (mon_yb b) Var.y singletonY
    · simp [R, R3]
    · simpa [mon_yb] using hb
    · intro v hv
      cases v <;> simp [removeVar, mon_yb, singletonY] at *

  have wz :
      ∃ α ∈ Rk R Var.y, SupportedIn α singletonZ := by
    apply derivativeWitness R (mon_zcy c) Var.y singletonZ
    · simp [R, R3]
    · simp [mon_zcy]
    · intro v hv
      cases v <;> simp [removeVar, mon_zcy, singletonZ] at *

  have wxy_x :
      ∃ α ∈ Rk R Var.x, SupportedIn α xy := by
    apply derivativeWitness R (mon_xay a) Var.x xy
    · simp [R, R3]
    · simpa [mon_xay] using ha
    · intro v hv
      cases v <;> simp [removeVar, mon_xay, xy] at *

  have wxy_y :
      ∃ α ∈ Rk R Var.y, SupportedIn α xy := by
    apply derivativeWitness R (mon_yb b) Var.y xy
    · simp [R, R3]
    · simpa [mon_yb] using hb
    · intro v hv
      cases v <;> simp [removeVar, mon_yb, xy] at *

  have wyz_y :
      ∃ α ∈ Rk R Var.y, SupportedIn α yz := by
    apply derivativeWitness R (mon_yb b) Var.y yz
    · simp [R, R3]
    · simpa [mon_yb] using hb
    · intro v hv
      cases v <;> simp [removeVar, mon_yb, yz] at *

  have wyz_z :
      ∃ α ∈ Rk R Var.z, SupportedIn α yz := by
    apply derivativeWitness R (mon_zcy c) Var.z yz
    · simp [R, R3]
    · simpa [mon_zcy] using hc
    · intro v hv
      cases v <;> simp [removeVar, mon_zcy, yz] at *

  have wxz_x :
      ∃ α ∈ Rk R Var.x, SupportedIn α xz := by
    apply derivativeWitness R (mon_xmzn m n) Var.x xz
    · simp [R, R3]
    · simpa [mon_xmzn] using hm
    · intro v hv
      cases v <;> simp [removeVar, mon_xmzn, xz] at *

  have wxz_z :
      ∃ α ∈ Rk R Var.z, SupportedIn α xz := by
    apply derivativeWitness R (mon_xmzn m n) Var.z xz
    · simp [R, R3]
    · simpa [mon_xmzn] using hn
    · intro v hv
      cases v <;> simp [removeVar, mon_xmzn, xz] at *

  intro J hJ
  simp [relevantJs] at hJ
  rcases hJ with hJ | hJ | hJ | hJ | hJ | hJ
  · subst J
    constructor
    · right
      refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars, singletonX]
      · simp [singletonX]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wx
    · refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars]
      · simp [singletonX]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wx

  · subst J
    constructor
    · left
      refine ⟨mon_yb b, ?_, ?_⟩
      · simp [R, R3]
      · intro v hv
        cases v <;> simp [mon_yb, singletonY] at *
    · refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars]
      · simp [singletonY]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wy

  · subst J
    constructor
    · right
      refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars, singletonZ]
      · simp [singletonZ]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wz
    · refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars]
      · simp [singletonZ]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wz

  · subst J
    constructor
    · left
      refine ⟨mon_yb b, ?_, ?_⟩
      · simp [R, R3]
      · intro v hv
        cases v <;> simp [mon_yb, xy] at *
    · refine ⟨xy, ?_, rfl, ?_⟩
      · intro v hv
        cases v <;> simp [allVars]
      · intro k hk
        simp [xy] at hk
        rcases hk with rfl | rfl
        · exact wxy_x
        · exact wxy_y

  · subst J
    constructor
    · left
      refine ⟨mon_xmzn m n, ?_, ?_⟩
      · simp [R, R3]
      · intro v hv
        cases v <;> simp [mon_xmzn, xz] at *
    · refine ⟨xz, ?_, rfl, ?_⟩
      · intro v hv
        cases v <;> simp [allVars]
      · intro k hk
        simp [xz] at hk
        rcases hk with rfl | rfl
        · exact wxz_x
        · exact wxz_z

  · subst J
    constructor
    · left
      refine ⟨mon_yb b, ?_, ?_⟩
      · simp [R, R3]
      · intro v hv
        cases v <;> simp [mon_yb, yz] at *
    · refine ⟨yz, ?_, rfl, ?_⟩
      · intro v hv
        cases v <;> simp [allVars]
      · intro k hk
        simp [yz] at hk
        rcases hk with rfl | rfl
        · exact wyz_y
        · exact wyz_z

/-!
Row 6:
  R6 = {x^a y, y^b z, z^c y, x^m z^n}.
-/
theorem R6_all_support_conditions
    (a b c m n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hm : 0 < m) (hn : 0 < n) :
    ∀ J ∈ relevantJs, C1 (R6 a b c m n) J ∧ C2 (R6 a b c m n) J := by

  let R := R6 a b c m n

  have wx :
      ∃ α ∈ Rk R Var.y, SupportedIn α singletonX := by
    apply derivativeWitness R (mon_xay a) Var.y singletonX
    · simp [R, R6]
    · simp [mon_xay]
    · intro v hv
      cases v <;> simp [removeVar, mon_xay, singletonX] at *

  have wy :
      ∃ α ∈ Rk R Var.z, SupportedIn α singletonY := by
    apply derivativeWitness R (mon_ybz b) Var.z singletonY
    · simp [R, R6]
    · simp [mon_ybz]
    · intro v hv
      cases v <;> simp [removeVar, mon_ybz, singletonY] at *

  have wz :
      ∃ α ∈ Rk R Var.y, SupportedIn α singletonZ := by
    apply derivativeWitness R (mon_zcy c) Var.y singletonZ
    · simp [R, R6]
    · simp [mon_zcy]
    · intro v hv
      cases v <;> simp [removeVar, mon_zcy, singletonZ] at *

  have wxy_x :
      ∃ α ∈ Rk R Var.x, SupportedIn α xy := by
    apply derivativeWitness R (mon_xay a) Var.x xy
    · simp [R, R6]
    · simpa [mon_xay] using ha
    · intro v hv
      cases v <;> simp [removeVar, mon_xay, xy] at *

  have wxy_z :
      ∃ α ∈ Rk R Var.z, SupportedIn α xy := by
    apply derivativeWitness R (mon_ybz b) Var.z xy
    · simp [R, R6]
    · simp [mon_ybz]
    · intro v hv
      cases v <;> simp [removeVar, mon_ybz, xy] at *

  have wyz_y :
      ∃ α ∈ Rk R Var.y, SupportedIn α yz := by
    apply derivativeWitness R (mon_zcy c) Var.y yz
    · simp [R, R6]
    · simp [mon_zcy]
    · intro v hv
      cases v <;> simp [removeVar, mon_zcy, yz] at *

  have wyz_z :
      ∃ α ∈ Rk R Var.z, SupportedIn α yz := by
    apply derivativeWitness R (mon_ybz b) Var.z yz
    · simp [R, R6]
    · simp [mon_ybz]
    · intro v hv
      cases v <;> simp [removeVar, mon_ybz, yz] at *

  have wxz_x :
      ∃ α ∈ Rk R Var.x, SupportedIn α xz := by
    apply derivativeWitness R (mon_xmzn m n) Var.x xz
    · simp [R, R6]
    · simpa [mon_xmzn] using hm
    · intro v hv
      cases v <;> simp [removeVar, mon_xmzn, xz] at *

  have wxz_z :
      ∃ α ∈ Rk R Var.z, SupportedIn α xz := by
    apply derivativeWitness R (mon_xmzn m n) Var.z xz
    · simp [R, R6]
    · simpa [mon_xmzn] using hn
    · intro v hv
      cases v <;> simp [removeVar, mon_xmzn, xz] at *

  intro J hJ
  simp [relevantJs] at hJ
  rcases hJ with hJ | hJ | hJ | hJ | hJ | hJ
  · subst J
    constructor
    · right
      refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars, singletonX]
      · simp [singletonX]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wx
    · refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars]
      · simp [singletonX]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wx

  · subst J
    constructor
    · right
      refine ⟨{Var.z}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.z := by simpa using hv
        subst v
        simp [allVars, singletonY]
      · simp [singletonY]
      · intro k hk
        have hk' : k = Var.z := by simpa using hk
        subst k
        exact wy
    · refine ⟨{Var.z}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.z := by simpa using hv
        subst v
        simp [allVars]
      · simp [singletonY]
      · intro k hk
        have hk' : k = Var.z := by simpa using hk
        subst k
        exact wy

  · subst J
    constructor
    · right
      refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars, singletonZ]
      · simp [singletonZ]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wz
    · refine ⟨{Var.y}, ?_, ?_, ?_⟩
      · intro v hv
        have hv' : v = Var.y := by simpa using hv
        subst v
        simp [allVars]
      · simp [singletonZ]
      · intro k hk
        have hk' : k = Var.y := by simpa using hk
        subst k
        exact wz

  · subst J
    constructor
    · left
      refine ⟨mon_xay a, ?_, ?_⟩
      · simp [R, R6]
      · intro v hv
        cases v <;> simp [mon_xay, xy] at *
    · refine ⟨xz, ?_, ?_, ?_⟩
      · intro v hv
        cases v <;> simp [allVars]
      · simp [xz, xy]
      · intro k hk
        simp [xz] at hk
        rcases hk with rfl | rfl
        · exact wxy_x
        · exact wxy_z

  · subst J
    constructor
    · left
      refine ⟨mon_xmzn m n, ?_, ?_⟩
      · simp [R, R6]
      · intro v hv
        cases v <;> simp [mon_xmzn, xz] at *
    · refine ⟨xz, ?_, rfl, ?_⟩
      · intro v hv
        cases v <;> simp [allVars]
      · intro k hk
        simp [xz] at hk
        rcases hk with rfl | rfl
        · exact wxz_x
        · exact wxz_z

  · subst J
    constructor
    · left
      refine ⟨mon_ybz b, ?_, ?_⟩
      · simp [R, R6]
      · intro v hv
        cases v <;> simp [mon_ybz, yz] at *
    · refine ⟨yz, ?_, rfl, ?_⟩
      · intro v hv
        cases v <;> simp [allVars]
      · intro k hk
        simp [yz] at hk
        rcases hk with rfl | rfl
        · exact wyz_y
        · exact wyz_z

end Section4
end FractionalTriangles
