import Mathlib

namespace FractionalTriangles

/!
Arithmetic checks for the five atomic weight systems listed in Section 4.
These are intentionally elementary: they verify weighted-homogeneity and the
`h-a-b-c` expressions, but they do NOT formalize the geometric mutation/Cox-recovery theorem.
-/

section FFF
variable (a b c : ℤ)
def FFF_A : ℤ := b*c
def FFF_B : ℤ := a*c
def FFF_C : ℤ := a*b
def FFF_h : ℤ := a*b*c

theorem FFF_hom_x : a * FFF_A a b c = FFF_h a b c := by
  simp [FFF_A, FFF_h]; ring

theorem FFF_hom_y : b * FFF_B a b c = FFF_h a b c := by
  simp [FFF_B, FFF_h]; ring

theorem FFF_hom_z : c * FFF_C a b c = FFF_h a b c := by
  simp [FFF_C, FFF_h]; ring

theorem FFF_shift :
    FFF_h a b c - FFF_A a b c - FFF_B a b c - FFF_C a b c
      = a*b*c - b*c - a*c - a*b := by
  simp [FFF_A, FFF_B, FFF_C, FFF_h]
end FFF

section C2F
variable (a b c : ℤ)
def C2F_A : ℤ := c*(b-1)
def C2F_B : ℤ := a*c
def C2F_C : ℤ := a*b
def C2F_h : ℤ := a*b*c

theorem C2F_hom_xy : a * C2F_A a b c + C2F_B a b c = C2F_h a b c := by
  simp [C2F_A, C2F_B, C2F_h]; ring

theorem C2F_hom_y : b * C2F_B a b c = C2F_h a b c := by
  simp [C2F_B, C2F_h]; ring

theorem C2F_hom_z : c * C2F_C a b c = C2F_h a b c := by
  simp [C2F_C, C2F_h]; ring
end C2F

section L2F
variable (a b c : ℤ)
def L2F_A : ℤ := c*(b-1)
def L2F_B : ℤ := c*(a-1)
def L2F_C : ℤ := a*b-1
def L2F_h : ℤ := c*(a*b-1)

theorem L2F_hom_xy : a * L2F_A a b c + L2F_B a b c = L2F_h a b c := by
  simp [L2F_A, L2F_B, L2F_h]; ring

theorem L2F_hom_yx : L2F_A a b c + b * L2F_B a b c = L2F_h a b c := by
  simp [L2F_A, L2F_B, L2F_h]; ring

theorem L2F_hom_z : c * L2F_C a b c = L2F_h a b c := by
  simp [L2F_C, L2F_h]
end L2F

section C3
variable (a b c : ℤ)
def C3_A : ℤ := c*(b-1)+1
def C3_B : ℤ := a*(c-1)
def C3_C : ℤ := a*b
def C3_h : ℤ := a*b*c

theorem C3_hom_xy : a * C3_A a b c + C3_B a b c = C3_h a b c := by
  simp [C3_A, C3_B, C3_h]; ring

theorem C3_hom_yz : b * C3_B a b c + C3_C a b c = C3_h a b c := by
  simp [C3_B, C3_C, C3_h]; ring

theorem C3_hom_z : c * C3_C a b c = C3_h a b c := by
  simp [C3_C, C3_h]
end C3

section L3
variable (a b c : ℤ)
def L3_A : ℤ := c*(b-1)+1
def L3_B : ℤ := a*(c-1)+1
def L3_C : ℤ := b*(a-1)+1
def L3_h : ℤ := a*b*c+1

theorem L3_hom_xy : a * L3_A a b c + L3_B a b c = L3_h a b c := by
  simp [L3_A, L3_B, L3_h]; ring

theorem L3_hom_yz : b * L3_B a b c + L3_C a b c = L3_h a b c := by
  simp [L3_B, L3_C, L3_h]; ring

theorem L3_hom_zx : c * L3_C a b c + L3_A a b c = L3_h a b c := by
  simp [L3_C, L3_A, L3_h]; ring
end L3

end FractionalTriangles
