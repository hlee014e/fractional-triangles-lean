import Mathlib

namespace FractionalTriangles.Section4.Lemma48GeometricStrataAudit

open Complex

/-!
Lemma 4.8 — direct coordinate-stratum audit for the five atomic curves.

Throughout a,b,c >= 2, exactly as in Lemma 4.8.  We check:
* every coordinate vertex Vx,Vy,Vz;
* every open coordinate line Lxy,Lxz,Lyz;
* the exact residual binomial on each listed line;
* nonvanishing on every unlisted open coordinate line.

This is the coordinate-incidence/exhaustiveness part of Table 2.
The quotient-orbit count and stabilizer-group statements are separate.
-/

def fff (a b c : ℕ) (x y z : ℂ) : ℂ :=
  x ^ a + y ^ b + z ^ c

def c2f (a b c : ℕ) (x y z : ℂ) : ℂ :=
  x ^ a * y + y ^ b + z ^ c

def l2f (a b c : ℕ) (x y z : ℂ) : ℂ :=
  x ^ a * y + x * y ^ b + z ^ c

def c3 (a b c : ℕ) (x y z : ℂ) : ℂ :=
  x ^ a * y + y ^ b * z + z ^ c

def l3 (a b c : ℕ) (x y z : ℂ) : ℂ :=
  x ^ a * y + y ^ b * z + z ^ c * x

lemma pos_of_two_le {n : ℕ} (h : 2 ≤ n) : 0 < n := by omega

lemma one_le_of_two_le {n : ℕ} (h : 2 ≤ n) : 1 ≤ n := by omega

lemma pow_factor (x : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    x ^ n = x * x ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [pow_succ']

section FFF

theorem fff_vertex_x_off
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    fff a b c 1 0 0 ≠ 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [fff, hb0, hc0]

theorem fff_vertex_y_off
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    fff a b c 0 1 0 ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [fff, ha0, hc0]

theorem fff_vertex_z_off
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    fff a b c 0 0 1 ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  simp [fff, ha0, hb0]

theorem fff_xy_restriction
    (a b c : ℕ) (hc : 2 ≤ c) (x y : ℂ) :
    fff a b c x y 0 = 0 ↔ x ^ a + y ^ b = 0 := by
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [fff, hc0]

theorem fff_xz_restriction
    (a b c : ℕ) (hb : 2 ≤ b) (x z : ℂ) :
    fff a b c x 0 z = 0 ↔ x ^ a + z ^ c = 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  simp [fff, hb0]

theorem fff_yz_restriction
    (a b c : ℕ) (ha : 2 ≤ a) (y z : ℂ) :
    fff a b c 0 y z = 0 ↔ y ^ b + z ^ c = 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  simp [fff, ha0]

end FFF

section C2F

theorem c2f_vertex_x_on
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    c2f a b c 1 0 0 = 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [c2f, hb0, hc0]

theorem c2f_vertex_y_off
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    c2f a b c 0 1 0 ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [c2f, ha0, hb0, hc0]

theorem c2f_vertex_z_off
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    c2f a b c 0 0 1 ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [c2f, ha0, hb0, hc0]

theorem c2f_xy_factor
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) (x y : ℂ) :
    c2f a b c x y 0 = y * (x ^ a + y ^ (b - 1)) := by
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  unfold c2f
  rw [show y ^ b = y * y ^ (b - 1) from pow_factor y b (one_le_of_two_le hb)]
  simp [hc0]
  ring

theorem c2f_xy_restriction
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (x y : ℂ) (hy : y ≠ 0) :
    c2f a b c x y 0 = 0 ↔ x ^ a + y ^ (b - 1) = 0 := by
  rw [c2f_xy_factor a b c hb hc x y]
  exact mul_eq_zero.trans (or_iff_right hy)

theorem c2f_yz_restriction
    (a b c : ℕ) (ha : 2 ≤ a) (y z : ℂ) :
    c2f a b c 0 y z = 0 ↔ y ^ b + z ^ c = 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  simp [c2f, ha0]

theorem c2f_xz_no_point
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (x z : ℂ) (hx : x ≠ 0) (hz : z ≠ 0) :
    c2f a b c x 0 z ≠ 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hzc : z ^ c ≠ 0 := pow_ne_zero c hz
  simpa [c2f, hb0] using hzc

end C2F

section L2F

theorem l2f_vertex_x_on
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    l2f a b c 1 0 0 = 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [l2f, hb0, hc0]

theorem l2f_vertex_y_on
    (a b c : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    l2f a b c 0 1 0 = 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [l2f, ha0, hc0]

theorem l2f_vertex_z_off
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    l2f a b c 0 0 1 ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [l2f, ha0, hb0, hc0]

theorem l2f_xy_factor
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (x y : ℂ) :
    l2f a b c x y 0 =
      x * y * (x ^ (a - 1) + y ^ (b - 1)) := by
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  unfold l2f
  rw [show x ^ a = x * x ^ (a - 1) from pow_factor x a (one_le_of_two_le ha)]
  rw [show y ^ b = y * y ^ (b - 1) from pow_factor y b (one_le_of_two_le hb)]
  simp [hc0]
  ring

theorem l2f_xy_restriction
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    l2f a b c x y 0 = 0 ↔
      x ^ (a - 1) + y ^ (b - 1) = 0 := by
  rw [l2f_xy_factor a b c ha hb hc x y]
  simp [hx, hy]

theorem l2f_xz_no_point
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (x z : ℂ) (hz : z ≠ 0) :
    l2f a b c x 0 z ≠ 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hzc : z ^ c ≠ 0 := pow_ne_zero c hz
  simpa [l2f, hb0] using hzc

theorem l2f_yz_no_point
    (a b c : ℕ) (ha : 2 ≤ a)
    (y z : ℂ) (hz : z ≠ 0) :
    l2f a b c 0 y z ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hzc : z ^ c ≠ 0 := pow_ne_zero c hz
  simpa [l2f, ha0] using hzc

end L2F

section C3

theorem c3_vertex_x_on
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    c3 a b c 1 0 0 = 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [c3, hb0, hc0]

theorem c3_vertex_y_on
    (a b c : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    c3 a b c 0 1 0 = 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [c3, ha0, hc0]

theorem c3_vertex_z_off
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    c3 a b c 0 0 1 ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [c3, ha0, hb0, hc0]

theorem c3_yz_factor
    (a b c : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) (y z : ℂ) :
    c3 a b c 0 y z =
      z * (y ^ b + z ^ (c - 1)) := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  unfold c3
  rw [show z ^ c = z * z ^ (c - 1) from pow_factor z c (one_le_of_two_le hc)]
  simp [ha0]
  ring

theorem c3_yz_restriction
    (a b c : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c)
    (y z : ℂ) (hz : z ≠ 0) :
    c3 a b c 0 y z = 0 ↔
      y ^ b + z ^ (c - 1) = 0 := by
  rw [c3_yz_factor a b c ha hc y z]
  exact mul_eq_zero.trans (or_iff_right hz)

theorem c3_xy_no_point
    (a b c : ℕ) (hc : 2 ≤ c)
    (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    c3 a b c x y 0 ≠ 0 := by
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  have hxy : x ^ a * y ≠ 0 := mul_ne_zero (pow_ne_zero a hx) hy
  simpa [c3, hc0] using hxy

theorem c3_xz_no_point
    (a b c : ℕ) (hb : 2 ≤ b)
    (x z : ℂ) (hz : z ≠ 0) :
    c3 a b c x 0 z ≠ 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hzc : z ^ c ≠ 0 := pow_ne_zero c hz
  simpa [c3, hb0] using hzc

end C3

section L3

theorem l3_vertex_x_on
    (a b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    l3 a b c 1 0 0 = 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [l3, hb0, hc0]

theorem l3_vertex_y_on
    (a b c : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) :
    l3 a b c 0 1 0 = 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  simp [l3, ha0, hc0]

theorem l3_vertex_z_on
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    l3 a b c 0 0 1 = 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  simp [l3, ha0, hb0]

theorem l3_xy_no_point
    (a b c : ℕ) (hc : 2 ≤ c)
    (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    l3 a b c x y 0 ≠ 0 := by
  have hc0 : c ≠ 0 := (pos_of_two_le hc).ne'
  have hxy : x ^ a * y ≠ 0 := mul_ne_zero (pow_ne_zero a hx) hy
  simpa [l3, hc0] using hxy

theorem l3_yz_no_point
    (a b c : ℕ) (ha : 2 ≤ a)
    (y z : ℂ) (hy : y ≠ 0) (hz : z ≠ 0) :
    l3 a b c 0 y z ≠ 0 := by
  have ha0 : a ≠ 0 := (pos_of_two_le ha).ne'
  have hyz : y ^ b * z ≠ 0 := mul_ne_zero (pow_ne_zero b hy) hz
  simpa [l3, ha0] using hyz

theorem l3_xz_no_point
    (a b c : ℕ) (hb : 2 ≤ b)
    (x z : ℂ) (hx : x ≠ 0) (hz : z ≠ 0) :
    l3 a b c x 0 z ≠ 0 := by
  have hb0 : b ≠ 0 := (pos_of_two_le hb).ne'
  have hzx : z ^ c * x ≠ 0 := mul_ne_zero (pow_ne_zero c hz) hx
  simpa [l3, hb0] using hzx

end L3

/-! Packaged row-by-row Table 2 coordinate audit. -/

section PackagedAudit

theorem c2f_coordinate_audit
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    c2f a b c 1 0 0 = 0 ∧
    c2f a b c 0 1 0 ≠ 0 ∧
    c2f a b c 0 0 1 ≠ 0 ∧
    (∀ x z : ℂ, x ≠ 0 → z ≠ 0 → c2f a b c x 0 z ≠ 0) := by
  exact ⟨c2f_vertex_x_on a b c hb hc,
         c2f_vertex_y_off a b c ha hb hc,
         c2f_vertex_z_off a b c ha hb hc,
         fun x z hx hz => c2f_xz_no_point a b c ha hb hc x z hx hz⟩

theorem l2f_coordinate_audit
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    l2f a b c 1 0 0 = 0 ∧
    l2f a b c 0 1 0 = 0 ∧
    l2f a b c 0 0 1 ≠ 0 ∧
    (∀ x z : ℂ, z ≠ 0 → l2f a b c x 0 z ≠ 0) ∧
    (∀ y z : ℂ, z ≠ 0 → l2f a b c 0 y z ≠ 0) := by
  exact ⟨l2f_vertex_x_on a b c hb hc,
         l2f_vertex_y_on a b c ha hc,
         l2f_vertex_z_off a b c ha hb hc,
         fun x z hz => l2f_xz_no_point a b c ha hb x z hz,
         fun y z hz => l2f_yz_no_point a b c ha y z hz⟩

theorem c3_coordinate_audit
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    c3 a b c 1 0 0 = 0 ∧
    c3 a b c 0 1 0 = 0 ∧
    c3 a b c 0 0 1 ≠ 0 ∧
    (∀ x y : ℂ, x ≠ 0 → y ≠ 0 → c3 a b c x y 0 ≠ 0) ∧
    (∀ x z : ℂ, z ≠ 0 → c3 a b c x 0 z ≠ 0) := by
  exact ⟨c3_vertex_x_on a b c hb hc,
         c3_vertex_y_on a b c ha hc,
         c3_vertex_z_off a b c ha hb hc,
         fun x y hx hy => c3_xy_no_point a b c hc x y hx hy,
         fun x z hz => c3_xz_no_point a b c hb x z hz⟩

theorem l3_coordinate_audit
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    l3 a b c 1 0 0 = 0 ∧
    l3 a b c 0 1 0 = 0 ∧
    l3 a b c 0 0 1 = 0 ∧
    (∀ x y : ℂ, x ≠ 0 → y ≠ 0 → l3 a b c x y 0 ≠ 0) ∧
    (∀ y z : ℂ, y ≠ 0 → z ≠ 0 → l3 a b c 0 y z ≠ 0) ∧
    (∀ x z : ℂ, x ≠ 0 → z ≠ 0 → l3 a b c x 0 z ≠ 0) := by
  exact ⟨l3_vertex_x_on a b c hb hc,
         l3_vertex_y_on a b c ha hc,
         l3_vertex_z_on a b c ha hb,
         fun x y hx hy => l3_xy_no_point a b c hc x y hx hy,
         fun y z hy hz => l3_yz_no_point a b c ha y z hy hz,
         fun x z hx hz => l3_xz_no_point a b c hb x z hx hz⟩

end PackagedAudit

end FractionalTriangles.Section4.Lemma48GeometricStrataAudit
