import Mathlib.Tactic

/-!
# Explicit pointed quartic and cubic rational maps

For y²=a t⁴+b t³+c t²+d t+q², the formulas below construct the usual
monic cubic directly from the point (0,q). All identities are field arithmetic. They will be
specialized to the quartics in Jaswal Proposition 7.2(a), Theorem 8.1(a),
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6
section Field
variable {K:Type*}[Field K][CharZero K]

def pointedQuartic (a b c d q t:K):K := a*t^4+b*t^3+c*t^2+d*t+q^2
def pointedCubic (a b c d q X:K):K :=
  X^3+c*X^2+(b*d-4*a*q^2)*X+(a*d^2+b^2*q^2-4*a*c*q^2)
def pointedInverseDen (a q X:K):K := X^2-4*a*q^2
def pointedInverseLinear (b d q X:K):K := d*X+2*b*q^2
def pointedInverseNum (b d q X Y:K):K := 2*q*Y+pointedInverseLinear b d q X
def pointedInverseT (a b d q X Y:K):K := pointedInverseNum b d q X Y/pointedInverseDen a q X
def pointedInverseEta (a b d q X Y:K):K :=
  (X*(pointedInverseT a b d q X Y)^2-d*pointedInverseT a b d q X Y-2*q^2)/(2*q)
def pointedForwardX (d q t eta:K):K := (2*q*(eta+q)+d*t)/t^2
def pointedForwardY (a b d q t eta:K):K :=
  (pointedInverseDen a q (pointedForwardX d q t eta)*t-
    pointedInverseLinear b d q (pointedForwardX d q t eta))/(2*q)

omit [CharZero K] in
theorem pointed_inverse_identity (a b c d q X Y:K):
    (pointedInverseNum b d q X Y)^2-
      2*pointedInverseLinear b d q X*pointedInverseNum b d q X Y+
      pointedInverseDen a q X*(d^2-4*q^2*X-4*c*q^2)=
      4*q^2*(Y^2-pointedCubic a b c d q X) := by
  simp only [pointedInverseNum,pointedInverseLinear,pointedInverseDen,pointedCubic]
  ring

omit [CharZero K] in
theorem pointed_inverse_quadratic (a b c d q X Y:K)
    (hA:pointedInverseDen a q X≠0)(hE:Y^2=pointedCubic a b c d q X):
    pointedInverseDen a q X*(pointedInverseT a b d q X Y)^2-
      2*pointedInverseLinear b d q X*pointedInverseT a b d q X Y+
      (d^2-4*q^2*X-4*c*q^2)=0 := by
  have hrel:pointedInverseDen a q X*pointedInverseT a b d q X Y=
      pointedInverseNum b d q X Y := by
    dsimp only [pointedInverseT]
    field_simp
  have hp:=pointed_inverse_identity a b c d q X Y
  rw [hE,sub_self,mul_zero,←hrel] at hp
  have hz:pointedInverseDen a q X*
      (pointedInverseDen a q X*(pointedInverseT a b d q X Y)^2-
        2*pointedInverseLinear b d q X*pointedInverseT a b d q X Y+
        (d^2-4*q^2*X-4*c*q^2))=0 := by linear_combination hp
  exact (mul_eq_zero.mp hz).resolve_left hA

theorem pointed_inverse_equation (a b c d q X Y:K)(hq:q≠0)
    (hA:pointedInverseDen a q X≠0)(hE:Y^2=pointedCubic a b c d q X):
    (pointedInverseEta a b d q X Y)^2=
      pointedQuartic a b c d q (pointedInverseT a b d q X Y) := by
  have hQ:=pointed_inverse_quadratic a b c d q X Y hA hE
  dsimp only [pointedInverseEta]
  generalize ht:pointedInverseT a b d q X Y=t at *
  simp only [pointedInverseDen,pointedInverseLinear] at hQ
  simp only [pointedQuartic]
  field_simp
  linear_combination t^2*hQ

theorem pointed_inverse_forward_X (a b d q X Y:K)(hq:q≠0)
    (ht:pointedInverseT a b d q X Y≠0):
    pointedForwardX d q (pointedInverseT a b d q X Y)
      (pointedInverseEta a b d q X Y)=X := by
  simp only [pointedForwardX,pointedInverseEta]
  generalize he:pointedInverseT a b d q X Y=t at *
  field_simp
  ring

theorem pointed_inverse_forward_Y (a b d q X Y:K)(hq:q≠0)
    (hA:pointedInverseDen a q X≠0)(ht:pointedInverseT a b d q X Y≠0):
    pointedForwardY a b d q (pointedInverseT a b d q X Y)
      (pointedInverseEta a b d q X Y)=Y := by
  simp only [pointedForwardY,pointed_inverse_forward_X a b d q X Y hq ht]
  simp only [pointedInverseT,pointedInverseNum]
  field_simp
  ring

theorem pointed_inverse_den_ne_zero (a q X:K)(hq:q≠0)(ha:¬IsSquare a):
    pointedInverseDen a q X≠0 := by
  intro hA
  apply ha
  refine ⟨X/(2*q),?_⟩
  simp only [pointedInverseDen] at hA
  field_simp
  linear_combination -hA

theorem pointed_inverse_num_zero_X (a b c d q X Y:K)(hq:q≠0)
    (hA:pointedInverseDen a q X≠0)(hE:Y^2=pointedCubic a b c d q X)
    (hN:pointedInverseNum b d q X Y=0):
    X=(d^2-4*c*q^2)/(4*q^2) := by
  have hi:=pointed_inverse_identity a b c d q X Y
  rw [hN,hE] at hi
  have hz:pointedInverseDen a q X*(d^2-4*q^2*X-4*c*q^2)=0 := by
    simpa only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_sub,sub_zero,neg_zero,zero_add,sub_self] using hi
  have hC: d^2-4*q^2*X-4*c*q^2=0 := (mul_eq_zero.mp hz).resolve_left hA
  field_simp
  linear_combination -hC

end Field
end Z2Z4Rank6
