import Mathlib

namespace FractionalTriangles.Section4.Prop47F3CaseII

theorem f3_caseII_contradiction
    (a e A B c C h m n : ℕ)
    (ha : 0 < a)
    (hC : 1 < C)
    (hae : Nat.Coprime a e)
    (hAB : a * A = e * B)
    (hCB : c * C = e * B)
    (hBC : Nat.Coprime B C)
    (hh : h = (e + 1) * B)
    (hlink : m * A + n * C = h) :
    False := by

  have ha_eB : a ∣ e * B := by
    use A
    exact hAB.symm

  have ha_Be : a ∣ B * e := by
    simpa [Nat.mul_comm] using ha_eB

  have haB : a ∣ B :=
    (Nat.Coprime.dvd_mul_right hae).mp ha_Be

  obtain ⟨U, hBU⟩ := haB

  have hcancel : a * A = a * (e * U) := by
    calc
      a * A = e * B := hAB
      _ = e * (a * U) := by simp [hBU]
      _ = a * (e * U) := by ac_rfl

  have hAU : A = e * U := by
    exact Nat.mul_left_cancel ha hcancel

  have hC_dvd_eB : C ∣ e * B := by
    use c
    simpa [Nat.mul_comm] using hCB.symm

  have hC_dvd_Be : C ∣ B * e := by
    simpa [Nat.mul_comm] using hC_dvd_eB

  have hCe : C ∣ e :=
    (Nat.Coprime.dvd_mul_left hBC.symm).mp hC_dvd_Be

  have hCA : C ∣ A := by
    rw [hAU]
    exact dvd_mul_of_dvd_left hCe U

  have hCmA : C ∣ m * A := by
    exact dvd_mul_of_dvd_right hCA m

  have hCnC : C ∣ n * C := by
    use n
    simp [Nat.mul_comm]

  have hCh : C ∣ h := by
    rw [← hlink]
    exact Nat.dvd_add hCmA hCnC

  have hCcop_e1 : Nat.Coprime C (e + 1) := by
    obtain ⟨k, hk⟩ := hCe
    subst e
    simp [Nat.coprime_add_self_right]

  have hCcop_hprod : Nat.Coprime C ((e + 1) * B) :=
    hCcop_e1.mul_right hBC.symm

  have hC_one : C = 1 := by
    apply Nat.Coprime.eq_one_of_dvd hCcop_hprod
    simpa [hh] using hCh

  omega

end FractionalTriangles.Section4.Prop47F3CaseII
