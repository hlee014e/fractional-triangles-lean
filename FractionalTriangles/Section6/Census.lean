import Mathlib
import FractionalTriangles.Section5.L3Section6

namespace FractionalTriangles
namespace Section6

/-!
# Section 6 — Theorem 6.2 census arithmetic audit
Paper p.22.

This file does NOT attempt to reimplement the full divisor enumerator inside Lean.
It formalizes the published census table as data and checks the numerical
consequences claimed in the theorem:
* the per-index counts are exactly the displayed table;
* the total count for 2 <= δ <= 30 is 506;
* the displayed zero-count indices in this range are 6, 12, 30.

No `sorry`, no axioms.
-/

def censusCount : ℕ → ℕ
| 2  => 6
| 3  => 8
| 4  => 8
| 5  => 21
| 6  => 0
| 7  => 29
| 8  => 11
| 9  => 12
| 10 => 6
| 11 => 37
| 12 => 0
| 13 => 36
| 14 => 10
| 15 => 9
| 16 => 11
| 17 => 40
| 18 => 2
| 19 => 46
| 20 => 11
| 21 => 12
| 22 => 9
| 23 => 55
| 24 => 3
| 25 => 28
| 26 => 16
| 27 => 18
| 28 => 10
| 29 => 52
| 30 => 0
| _  => 0

/-- Exact transcription of the published table. -/
theorem census_table_values :
    [censusCount 2, censusCount 3, censusCount 4, censusCount 5,
     censusCount 6, censusCount 7, censusCount 8, censusCount 9,
     censusCount 10, censusCount 11, censusCount 12, censusCount 13,
     censusCount 14, censusCount 15, censusCount 16, censusCount 17,
     censusCount 18, censusCount 19, censusCount 20, censusCount 21,
     censusCount 22, censusCount 23, censusCount 24, censusCount 25,
     censusCount 26, censusCount 27, censusCount 28, censusCount 29,
     censusCount 30]
    =
    [6,8,8,21,0,29,11,12,6,37,0,36,10,9,11,40,2,46,11,12,
     9,55,3,28,16,18,10,52,0] := by
  decide

/-- The published per-index counts sum to 506. -/
theorem census_total_506 :
    (List.range 29).map (fun k => censusCount (k+2)) |>.sum = 506 := by
  decide

/-- In the displayed range, δ=6,12,30 have zero classes. -/
theorem census_zero_indices :
    censusCount 6 = 0 ∧ censusCount 12 = 0 ∧ censusCount 30 = 0 := by
  decide

/-- A few spot checks on nonzero entries. -/
theorem census_spot_checks :
    censusCount 7 = 29 ∧ censusCount 23 = 55 ∧ censusCount 29 = 52 := by
  decide

/-!
External/computational input for the FULL Theorem 6.2:
* enumeration of every finite divisor construction in Theorem 5.6;
* application of every primitivity criterion in Proposition 5.7;
* deduplication by the canonical sorted primitive weight key;
* proof that equal keys are exactly graded-isomorphism classes;
* the supplementary 506-row / 652-witness certificates.

Those are not recreated here from scratch.  This file only verifies the
arithmetic consistency of the displayed theorem table and total.
-/

end Section6
end FractionalTriangles
