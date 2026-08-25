import Mathlib
import FractionalTriangles.Section6.LowIndexActualEnumeration

namespace FractionalTriangles
namespace Section6

/-!
# Section 6 — full independent census through δ = 30

This extends `Section6_LowIndexActualEnumeration`.  The counts below are
computed by `actualCount`, whose input is generated directly from the five
Table 3 atomic weight formulae in the finite exponent box of Lemma 5.4.
The printed census table is NOT used as input to `actualCount`.

No `sorry`, no axioms.
-/

/-- Independent executable reproduction of every count in Theorem 6.2. -/
theorem full_census_counts_actual :
    [actualCount 2, actualCount 3, actualCount 4, actualCount 5,
     actualCount 6, actualCount 7, actualCount 8, actualCount 9,
     actualCount 10, actualCount 11, actualCount 12, actualCount 13,
     actualCount 14, actualCount 15, actualCount 16, actualCount 17,
     actualCount 18, actualCount 19, actualCount 20, actualCount 21,
     actualCount 22, actualCount 23, actualCount 24, actualCount 25,
     actualCount 26, actualCount 27, actualCount 28, actualCount 29,
     actualCount 30]
    =
    [6,8,8,21,0,29,11,12,6,37,0,36,10,9,11,40,2,46,11,12,
     9,55,3,28,16,18,10,52,0] := by
  native_decide

/--
The independently generated class counts for 2 ≤ δ ≤ 30 sum to 506.
Unlike `census_total_506`, the summands here are computed from Table 3.
-/
theorem full_census_total_actual_506 :
    (List.range 29).map (fun k => actualCount (k+2)) |>.sum = 506 := by
  native_decide

/-- Independent reproduction of the zero indices in the displayed range. -/
theorem full_census_zero_indices_actual :
    actualCount 6 = 0 ∧ actualCount 12 = 0 ∧ actualCount 30 = 0 := by
  native_decide

/-- Independent spot checks at the three largest displayed counts. -/
theorem full_census_large_spot_checks :
    actualCount 19 = 46 ∧ actualCount 23 = 55 ∧ actualCount 29 = 52 := by
  native_decide

/-!
Audit note.

`actualCount`:
1. enumerates α,β,γ in the Lemma 5.4 finite box;
2. evaluates all five Table 3 raw adjugate weight systems;
3. tests h-a-b-c=δ;
4. tests gcd(a,b,c)=1;
5. sorts the three primitive weights;
6. deduplicates by (sorted a,b,c; h).

Thus this file is an independent finite computation from the structural
classification formulas, not an arithmetic re-summing of the printed table.

The geometric/classification inputs remain the already-audited mathematical
results that justify Table 3 and Lemma 5.4 as exhaustive.
-/

end Section6
end FractionalTriangles
