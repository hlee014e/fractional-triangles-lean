import Mathlib
import FractionalTriangles.Section6.Theorem62_Enumeration

namespace FractionalTriangles
namespace Section6

/-!
# Section 6: independent low-index enumeration

This file computes from Table 3 itself, rather than importing the printed
census counts.  Lemma 5.4 gives the finite exponent box α,β,γ ≤ δ+6
(FFF is ordered); Table 3 gives raw adjugate weights and h.  We retain
exactly primitive rows and deduplicate by sorted primitive weights plus h.

This is an independent executable check for δ=2,...,6.
-/

def primitive3 (a b c : Nat) : Bool :=
  Nat.gcd a (Nat.gcd b c) == 1

def mkIf (δ a b c h : Nat) : List Candidate :=
  if h = a+b+c+δ ∧ primitive3 a b c
  then [⟨a,b,c,h,true⟩] else []

def fffRow (δ α β γ : Nat) : List Candidate :=
  mkIf δ (β*γ) (α*γ) (α*β) (α*β*γ)

def c2fRow (δ α β γ : Nat) : List Candidate :=
  mkIf δ (γ*(β-1)) (α*γ) (α*β) (α*β*γ)

def l2fRow (δ α β γ : Nat) : List Candidate :=
  mkIf δ (γ*(β-1)) (γ*(α-1)) (α*β-1) (γ*(α*β-1))

def c3Row (δ α β γ : Nat) : List Candidate :=
  mkIf δ (β*γ-γ+1) (α*(γ-1)) (α*β) (α*β*γ)

def l3Row (δ α β γ : Nat) : List Candidate :=
  mkIf δ (β*γ-γ+1) (α*γ-α+1) (α*β-β+1) (α*β*γ+1)

def exps (δ : Nat) : List Nat := (List.range (δ+5)).map (fun k => k+2)

def candidatesActual (δ : Nat) : List Candidate :=
  let es := exps δ
  let fff :=
    es.flatMap fun α =>
    es.flatMap fun β =>
    es.flatMap fun γ =>
      if α ≤ β ∧ β ≤ γ then fffRow δ α β γ else []
  let rest :=
    es.flatMap fun α =>
    es.flatMap fun β =>
    es.flatMap fun γ =>
      c2fRow δ α β γ ++ l2fRow δ α β γ ++
      c3Row δ α β γ ++ l3Row δ α β γ
  fff ++ rest

def actualCount (δ : Nat) : Nat := classCount (candidatesActual δ)

/-- The first five noncanonical indices are independently reproduced. -/
theorem low_index_counts_actual :
    [actualCount 2, actualCount 3, actualCount 4,
     actualCount 5, actualCount 6] = [6,8,8,21,0] := by
  native_decide

/-- Individual executable certificates, useful when auditing failures. -/
/-! Recover the six index-two keys, independently from Table 3. -/
def keysAt2 := uniqueKeys (candidatesActual 2)

theorem index2_keys_actual :
  keysAt2 =
   [(3,5,5,15), (3,5,7,17), (3,5,10,20),
    (3,7,9,21), (3,7,12,24), (3,10,15,30)] := by
  native_decide

end Section6
end FractionalTriangles
