import Mathlib

namespace FractionalTriangles

/-- The numerical defect used throughout the paper, written without division. -/
def defectNumerator (p q r N : ℕ) : ℤ :=
  (N : ℤ) - (N / p : ℕ) - (N / q : ℕ) - (N / r : ℕ)

/-- A tiny arithmetic consequence used repeatedly: if `k = δ * u`, then `δ ∣ k`. -/
theorem delta_dvd_k_of_eq_mul (δ k u : ℕ) (h : k = δ * u) : δ ∣ k := by
  refine ⟨u, ?_⟩
  simpa [h, Nat.mul_comm]

/-- Conversely, a divisibility hypothesis can be unpacked as `k = δ*u`. -/
theorem exists_u_of_delta_dvd_k (δ k : ℕ) (h : δ ∣ k) : ∃ u : ℕ, k = δ * u := by
  rcases h with ⟨u, hu⟩
  exact ⟨u, hu.symm⟩

/-- In the three-variable specialization, Theorem 1.2 says `h-a-b-c = δ`.
This lemma is the rearranged form used in many later Diophantine calculations. -/
theorem relation_degree_from_shift
    (a b c h δ : ℤ) (hshift : h - a - b - c = δ) :
    h = a + b + c + δ := by
  linarith

/-- The converse rearrangement. -/
theorem shift_from_relation_degree
    (a b c h δ : ℤ) (hh : h = a + b + c + δ) :
    h - a - b - c = δ := by
  linarith

end FractionalTriangles
