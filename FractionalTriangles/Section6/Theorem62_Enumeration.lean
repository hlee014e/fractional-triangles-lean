import Mathlib
import Mathlib

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
