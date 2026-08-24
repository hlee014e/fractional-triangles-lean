import Mathlib
import FractionalTriangles.Section4_Lemma42

namespace FractionalTriangles
namespace Section4Lemma42Serre

/--
Finite-residue uniformization used in the Serre-vanishing step of Lemma 4.2.

Suppose that for every residue class `r < M` there is a threshold `Q_r`
such that a property `P q r` holds for every `q ≥ Q_r`.
Then there is one common threshold `Q` which works for all residue classes.
-/
theorem finite_residue_uniform_bound
    (M : ℕ)
    (P : ℕ → ℕ → Prop)
    (h :
      ∀ r, r < M →
        ∃ Q, ∀ q, Q ≤ q → P q r) :
    ∃ Q, ∀ r, r < M → ∀ q, Q ≤ q → P q r := by
  classical
  by_cases hM : M = 0
  · subst M
    refine ⟨0, ?_⟩
    intro r hr
    omega
  ·
    let f : Fin M → ℕ := fun r =>
      Nat.find (h r.1 r.2)

    let Q : ℕ := Finset.univ.sup f

    refine ⟨Q, ?_⟩
    intro r hr q hQq

    let rr : Fin M := ⟨r, hr⟩

    have hfQ : f rr ≤ Q := by
      exact Finset.le_sup (s := Finset.univ) (f := f) (by simp)

    have hfq : f rr ≤ q := le_trans hfQ hQq

    exact Nat.find_spec (h r hr) q hfq


/--
Arithmetic form of the decomposition of a degree into quotient and residue:
for `M > 0`, every `m` can be written uniquely in the form

    m = (m / M) * M + (m % M),

with residue `< M`.
-/
theorem degree_division_with_residue
    (m M : ℕ) (hM : 0 < M) :
    m = (m / M) * M + (m % M) ∧
    m % M < M := by
  constructor
  · omega
  · exact Nat.mod_lt m hM


/--
If a property is eventually true in every residue class modulo `M`,
then it is eventually true for the quotient/remainder pair attached to every
sufficiently large degree.

This is the purely arithmetic/logical content of the phrase
"Serre vanishing, applied in the finitely many residue classes of m".
-/
theorem eventually_in_all_residue_classes
    (M : ℕ)
    (hM : 0 < M)
    (P : ℕ → ℕ → Prop)
    (h :
      ∀ r, r < M →
        ∃ Q, ∀ q, Q ≤ q → P q r) :
    ∃ Q, ∀ m,
      Q * M ≤ m →
      P (m / M) (m % M) := by
  obtain ⟨Q, hQ⟩ :=
    finite_residue_uniform_bound M P h

  refine ⟨Q, ?_⟩
  intro m hm

  have hr : m % M < M := Nat.mod_lt m hM

  have hq : Q ≤ m / M := by
    by_contra hnot
    have hlt : m / M < Q := Nat.lt_of_not_ge hnot
    have hdiv :
        m = (m / M) * M + (m % M) := by
      omega
    have hrem : m % M < M := Nat.mod_lt m hM
    omega

  exact hQ (m % M) hr (m / M) hq

end Section4Lemma42Serre
end FractionalTriangles
