import Mathlib

namespace FractionalTriangles

variable {G : Type*} [CommGroup G]

/--
If an element is killed by two coprime powers, then it is trivial.
-/
theorem group_element_eq_one_of_coprime_powers
    (a : G) (δ N : ℕ)
    (hcop : Nat.Coprime δ N)
    (hδ : a ^ δ = 1)
    (hN : a ^ N = 1) :
    a = 1 := by
  have hordδ : orderOf a ∣ δ :=
    (orderOf_dvd_iff_pow_eq_one).2 hδ
  have hordN : orderOf a ∣ N :=
    (orderOf_dvd_iff_pow_eq_one).2 hN
  have hordg : orderOf a ∣ Nat.gcd δ N :=
    Nat.dvd_gcd hordδ hordN
  rw [hcop.gcd_eq_one] at hordg
  have ho : orderOf a = 1 :=
    Nat.eq_one_of_dvd_one hordg
  exact orderOf_eq_one_iff.mp ho

end FractionalTriangles
