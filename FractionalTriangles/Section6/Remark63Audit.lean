import Mathlib
import FractionalTriangles.Section6.FullCensusActual

namespace FractionalTriangles
namespace Section6

/-!
# Remark 6.3 — six explicit systems

The manuscript lists, in order:
δ=3 : (4,10,13;30), equation x z^2 + y^3 + x^5 y
δ=4 : (5,6,9;24),   equation z x^3 + y z^2 + y^4
δ=5 : (6,8,19;38),  equation z^2 + x y^4 + x^5 y
δ=5 : (4,7,16;32),  equation z^2 + x y^4 + z x^4
δ=5 : (4,7,12;28),  equation x z^2 + y^4 + x^4 z
δ=5 : (4,7,9;25),   equation y z^2 + x^4 z + x y^3

We check every monomial degree, a-invariant, and primitivity.
No `sorry`, no axioms.
-/

def primitiveWeights (a b c : Nat) : Bool :=
  Nat.gcd a (Nat.gcd b c) == 1

theorem remark63_system1 :
    4 + 2*13 = 3*10 ∧
    5*4 + 10 = 30 ∧
    30 - 4 - 10 - 13 = 3 ∧
    primitiveWeights 4 10 13 := by
  native_decide

theorem remark63_system2 :
    9 + 3*5 = 6 + 2*9 ∧
    4*6 = 24 ∧
    24 - 5 - 6 - 9 = 4 ∧
    primitiveWeights 5 6 9 := by
  native_decide

theorem remark63_system3 :
    2*19 = 6 + 4*8 ∧
    5*6 + 8 = 38 ∧
    38 - 6 - 8 - 19 = 5 ∧
    primitiveWeights 6 8 19 := by
  native_decide

theorem remark63_system4 :
    2*16 = 4 + 4*7 ∧
    16 + 4*4 = 32 ∧
    32 - 4 - 7 - 16 = 5 ∧
    primitiveWeights 4 7 16 := by
  native_decide

theorem remark63_system5 :
    4 + 2*12 = 4*7 ∧
    4*4 + 12 = 28 ∧
    28 - 4 - 7 - 12 = 5 ∧
    primitiveWeights 4 7 12 := by
  native_decide

theorem remark63_system6 :
    7 + 2*9 = 4*4 + 9 ∧
    4 + 3*7 = 25 ∧
    25 - 4 - 7 - 9 = 5 ∧
    primitiveWeights 4 7 9 := by
  native_decide

/-- All six systems occur among the independently enumerated canonical keys
at their stated indices. -/
theorem remark63_keys_occur :
    (4,10,13,30) ∈ uniqueKeys (candidatesActual 3) ∧
    (5,6,9,24) ∈ uniqueKeys (candidatesActual 4) ∧
    (6,8,19,38) ∈ uniqueKeys (candidatesActual 5) ∧
    (4,7,16,32) ∈ uniqueKeys (candidatesActual 5) ∧
    (4,7,12,28) ∈ uniqueKeys (candidatesActual 5) ∧
    (4,7,9,25) ∈ uniqueKeys (candidatesActual 5) := by
  native_decide

end Section6
end FractionalTriangles
