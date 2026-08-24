import Mathlib

example (δ k : ℕ) (h : δ ∣ k) : ∃ u : ℕ, k = δ * u := by
  exact h
  