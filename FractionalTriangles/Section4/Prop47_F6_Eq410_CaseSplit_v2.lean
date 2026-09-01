import Mathlib

namespace FractionalTriangles
namespace Section4

def indGtOne (n : ℕ) : ℕ := if 1 < n then 1 else 0

/--
Arithmetic content of the case split after (4.10).

If
  [A>1] + [B>1] + [C>1] + d[W>1] = 3,
all parameters are positive, and W divides B and C, then:

* W = 1 forces A,B,C > 1;
* W > 1 forces d = 1 and A = 1.
-/
theorem f6_eq410_case_split
    (A B C d W : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hd : 0 < d) (hW : 0 < W)
    (hWB : W ∣ B) (hWC : W ∣ C)
    (hcount :
      indGtOne A + indGtOne B + indGtOne C
        + d * indGtOne W = 3) :
    (W = 1 ∧ 1 < A ∧ 1 < B ∧ 1 < C) ∨
    (1 < W ∧ d = 1 ∧ A = 1) := by
  by_cases hWgt : 1 < W
  · have hBgt : 1 < B := by
      have hle : W ≤ B := Nat.le_of_dvd hB hWB
      omega
    have hCgt : 1 < C := by
      have hle : W ≤ C := Nat.le_of_dvd hC hWC
      omega

    have hAeq : A = 1 := by
      by_contra hAne
      have hAgt : 1 < A := by omega
      simp [indGtOne, hWgt, hAgt, hBgt, hCgt] at hcount
      omega

    have hdeq : d = 1 := by
      simp [indGtOne, hWgt, hAeq, hBgt, hCgt] at hcount
      omega

    exact Or.inr ⟨hWgt, hdeq, hAeq⟩

  · have hWeq : W = 1 := by omega

    have hAgt : 1 < A := by
      by_contra hAnot
      by_cases hBgt : 1 < B
      · by_cases hCgt : 1 < C
        · simp [indGtOne, hWeq, hAnot, hBgt, hCgt] at hcount
        · simp [indGtOne, hWeq, hAnot, hBgt, hCgt] at hcount
      · by_cases hCgt : 1 < C
        · simp [indGtOne, hWeq, hAnot, hBgt, hCgt] at hcount
        · simp [indGtOne, hWeq, hAnot, hBgt, hCgt] at hcount

    have hBgt : 1 < B := by
      by_contra hBnot
      by_cases hAgt' : 1 < A
      · by_cases hCgt : 1 < C
        · simp [indGtOne, hWeq, hAgt', hBnot, hCgt] at hcount
        · simp [indGtOne, hWeq, hAgt', hBnot, hCgt] at hcount
      · by_cases hCgt : 1 < C
        · simp [indGtOne, hWeq, hAgt', hBnot, hCgt] at hcount
        · simp [indGtOne, hWeq, hAgt', hBnot, hCgt] at hcount

    have hCgt : 1 < C := by
      by_contra hCnot
      by_cases hAgt' : 1 < A
      · by_cases hBgt' : 1 < B
        · simp [indGtOne, hWeq, hAgt', hBgt', hCnot] at hcount
        · simp [indGtOne, hWeq, hAgt', hBgt', hCnot] at hcount
      · by_cases hBgt' : 1 < B
        · simp [indGtOne, hWeq, hAgt', hBgt', hCnot] at hcount
        · simp [indGtOne, hWeq, hAgt', hBgt', hCnot] at hcount

    exact Or.inl ⟨hWeq, hAgt, hBgt, hCgt⟩

end Section4
end FractionalTriangles
