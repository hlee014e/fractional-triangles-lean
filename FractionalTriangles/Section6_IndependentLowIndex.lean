import Mathlib
import FractionalTriangles.Section6_Census

namespace FractionalTriangles
namespace Section6

/-!
# Independent low-index census harness

Goal: do not merely sum the printed table.  Instead encode finite candidate
records, primitivity filtering, and canonical-key deduplication as executable
Lean functions.  This is the infrastructure needed to reproduce Theorem 6.2
from Theorem 5.6 + Proposition 5.7.

The exact five-family candidate generator is deliberately separated from the
generic verified counting machinery below.
-/

structure Candidate where
  a : Nat
  b : Nat
  c : Nat
  h : Nat
  primitive : Bool
deriving DecidableEq, Repr

def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  if a ≤ b then
    if b ≤ c then (a,b,c)
    else if a ≤ c then (a,c,b) else (c,a,b)
  else
    if a ≤ c then (b,a,c)
    else if b ≤ c then (b,c,a) else (c,b,a)

def canonicalKey (x : Candidate) : Nat × Nat × Nat × Nat :=
  let s := sort3 x.a x.b x.c
  (s.1, s.2.1, s.2.2, x.h)

def primitiveCandidates (xs : List Candidate) : List Candidate :=
  xs.filter (fun x => x.primitive)

def canonicalKeys (xs : List Candidate) : List (Nat × Nat × Nat × Nat) :=
  (primitiveCandidates xs).map canonicalKey

def uniqueKeys (xs : List Candidate) : List (Nat × Nat × Nat × Nat) :=
  (canonicalKeys xs).eraseDups

def classCount (xs : List Candidate) : Nat := (uniqueKeys xs).length

/-! Generic correctness checks for the executable pipeline. -/

example :
  sort3 7 2 5 = (2,5,7) := by decide

example :
  canonicalKey ⟨7,2,5,11,true⟩ = (2,5,7,11) := by decide

example :
  classCount [
    ⟨2,3,5,11,true⟩,
    ⟨5,2,3,11,true⟩, -- same canonical class
    ⟨2,3,7,13,false⟩,
    ⟨3,4,5,17,true⟩
  ] = 2 := by decide

/--
If two retained witnesses differ only by permutation of the three weights
and have the same relation degree, our canonical key identifies them.
-/
theorem canonical_permutation_example :
    canonicalKey ⟨2,5,3,17,true⟩ =
    canonicalKey ⟨5,3,2,17,true⟩ := by
  decide

/-!
The next layer must instantiate `candidates δ` from the five exact divisor
constructions of Theorem 5.6, with the Proposition 5.7 closed primitivity
tests.  Once that function is populated from the paper formulas, the target
statements are executable theorems:

  classCount (candidates 2) = 6
  classCount (candidates 3) = 8
  classCount (candidates 4) = 8
  classCount (candidates 5) = 21
  classCount (candidates 6) = 0

This bundle intentionally does NOT fake those five results by hard-coding
the printed counts.  It builds and checks the independent counting/dedup
machinery first.
-/

end Section6
end FractionalTriangles
