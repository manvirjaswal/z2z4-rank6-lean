module

public import Z2Z4Rank6.QuarticBirational
public import Z2Z4Rank6.SecondJacobianInfinite

@[expose] public section

/-!
# Rational maps from the second Jacobian to the printed quartic G2

The cubic produced from the rational quartic point (10/3,5812100/9) differs
from the printed J2 equation only by X=x−32474316674/9,Y=y. Source: Jaswal Theorem 8.1(a), DOI
10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6
section Field
variable {K:Type*}[Field K]

def secondQuartic (t:K):K :=1326538900*t^4-77611154441*t^2+1115619214900
def secondQuarticA : K :=1326538900
def secondQuarticB : K :=53061556000/3
def secondQuarticC : K :=32474316677/3
def secondQuarticD : K :=-8663852199380/27
def secondQuarticQ : K :=5812100/9
def secondPointedX (x:K):K :=x-32474316674/9
def secondQuarticT (x y:K):K :=
  pointedInverseT secondQuarticA secondQuarticB secondQuarticD secondQuarticQ (secondPointedX x) y
def secondQuarticTheta (x y:K):K :=secondQuarticT x y+10/3
def secondQuarticEta (x y:K):K :=
  pointedInverseEta secondQuarticA secondQuarticB secondQuarticD secondQuarticQ (secondPointedX x) y
def secondQuarticRecoverX (theta eta:K):K :=
  pointedForwardX secondQuarticD secondQuarticQ (theta-10/3) eta+32474316674/9
def secondQuarticRecoverY (theta eta:K):K :=
  pointedForwardY secondQuarticA secondQuarticB secondQuarticD secondQuarticQ (theta-10/3) eta

variable [CharZero K]

theorem secondQuartic_q_ne_zero : (secondQuarticQ:K)≠0 := by norm_num [secondQuarticQ]

theorem secondQuartic_shift_identity (t:K):
    pointedQuartic secondQuarticA secondQuarticB secondQuarticC secondQuarticD secondQuarticQ t=
      secondQuartic (t+10/3) := by
  norm_num [pointedQuartic,secondQuartic,secondQuarticA,secondQuarticB,secondQuarticC,
    secondQuarticD,secondQuarticQ]
  ring

theorem secondJacobian_pointed_equation (x y:K):
    y^2=(x+102809641014)*(x-51068871386)*(x-51740769627) ↔
      y^2=pointedCubic secondQuarticA secondQuarticB secondQuarticC secondQuarticD secondQuarticQ
        (secondPointedX x) := by
  have he:pointedCubic secondQuarticA secondQuarticB secondQuarticC secondQuarticD secondQuarticQ
      (secondPointedX x)=(x+102809641014)*(x-51068871386)*(x-51740769627) := by
    norm_num [pointedCubic,secondQuarticA,secondQuarticB,secondQuarticC,secondQuarticD,
      secondQuarticQ,secondPointedX]
    ring
  rw [he]

theorem secondQuartic_coordinates_equation (x y:K)
    (hE:y^2=(x+102809641014)*(x-51068871386)*(x-51740769627))
    (hA:pointedInverseDen secondQuarticA secondQuarticQ (secondPointedX x)≠0):
    (secondQuarticEta x y)^2=secondQuartic (secondQuarticTheta x y) := by
  have hi:=pointed_inverse_equation secondQuarticA secondQuarticB secondQuarticC secondQuarticD
    secondQuarticQ (secondPointedX x) y secondQuartic_q_ne_zero hA
    ((secondJacobian_pointed_equation x y).mp hE)
  rw [secondQuartic_shift_identity] at hi
  exact hi

theorem secondQuartic_recover_X (x y:K)
    (ht:secondQuarticT x y≠0):
    secondQuarticRecoverX (secondQuarticTheta x y) (secondQuarticEta x y)=x := by
  simp only [secondQuarticRecoverX,secondQuarticTheta,add_sub_cancel_right,secondQuarticEta]
  simp only [secondQuarticT] at ht ⊢
  rw [pointed_inverse_forward_X _ _ _ _ _ _ secondQuartic_q_ne_zero ht]
  simp only [secondPointedX,sub_add_cancel]

theorem secondQuartic_recover_Y (x y:K)
    (hA:pointedInverseDen secondQuarticA secondQuarticQ (secondPointedX x)≠0)
    (ht:secondQuarticT x y≠0):
    secondQuarticRecoverY (secondQuarticTheta x y) (secondQuarticEta x y)=y := by
  simp only [secondQuarticRecoverY,secondQuarticTheta,add_sub_cancel_right,secondQuarticEta]
  exact pointed_inverse_forward_Y _ _ _ _ _ _ secondQuartic_q_ne_zero hA ht

end Field

theorem secondQuartic_leading_nonsquare : ¬IsSquare (secondQuarticA:ℚ) := by
  norm_num [secondQuarticA]

theorem secondQuartic_inverse_den_ne_zero (x:ℚ):
    pointedInverseDen secondQuarticA secondQuarticQ (secondPointedX x)≠0 :=
  pointed_inverse_den_ne_zero _ _ _ secondQuartic_q_ne_zero secondQuartic_leading_nonsquare

@[ext] structure SecondQuarticPoint where
  theta : ℚ
  eta : ℚ
  equation : eta^2=secondQuartic theta

def secondJacobianQuarticChart : RationalPoints J2→Prop
  | .zero => False
  | .some x y _ => pointedInverseNum secondQuarticB secondQuarticD secondQuarticQ (secondPointedX x) y≠0

abbrev SecondJacobianQuarticChart := {P:RationalPoints J2 // secondJacobianQuarticChart P}

def secondJacobianToQuartic (P:SecondJacobianQuarticChart):SecondQuarticPoint := by
  rcases P with ⟨P,hP⟩
  cases P with
  | zero => exact hP.elim
  | some x y h => exact ⟨secondQuarticTheta x y,secondQuarticEta x y,
      secondQuartic_coordinates_equation x y ((secondJacobian_equation_iff x y).mp h.1)
        (secondQuartic_inverse_den_ne_zero x)⟩

theorem secondJacobian_chart_T_ne_zero (x y:ℚ)
    (h:pointedInverseNum secondQuarticB secondQuarticD secondQuarticQ (secondPointedX x) y≠0):
    secondQuarticT x y≠0 :=
  div_ne_zero h (secondQuartic_inverse_den_ne_zero x)

theorem secondJacobianToQuartic_injective:Function.Injective secondJacobianToQuartic := by
  rintro ⟨P,hP⟩ ⟨Q,hQ⟩ heq
  apply Subtype.ext
  cases P with
  | zero => exact hP.elim
  | some x1 y1 hp =>
    cases Q with
    | zero => exact hQ.elim
    | some x2 y2 hq =>
      have ht1:=secondJacobian_chart_T_ne_zero x1 y1 hP
      have ht2:=secondJacobian_chart_T_ne_zero x2 y2 hQ
      have hx:=congrArg (fun z:SecondQuarticPoint=>secondQuarticRecoverX z.theta z.eta) heq
      have hy:=congrArg (fun z:SecondQuarticPoint=>secondQuarticRecoverY z.theta z.eta) heq
      change secondQuarticRecoverX (secondQuarticTheta x1 y1) (secondQuarticEta x1 y1)=
        secondQuarticRecoverX (secondQuarticTheta x2 y2) (secondQuarticEta x2 y2) at hx
      change secondQuarticRecoverY (secondQuarticTheta x1 y1) (secondQuarticEta x1 y1)=
        secondQuarticRecoverY (secondQuarticTheta x2 y2) (secondQuarticEta x2 y2) at hy
      rw [secondQuartic_recover_X x1 y1 ht1,secondQuartic_recover_X x2 y2 ht2] at hx
      rw [secondQuartic_recover_Y x1 y1 (secondQuartic_inverse_den_ne_zero x1) ht1,
        secondQuartic_recover_Y x2 y2 (secondQuartic_inverse_den_ne_zero x2) ht2] at hy
      cases hx
      cases hy
      rfl

def secondJacobianQuarticBad : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff (5450739286869/100)
    (1223344450581962247/1000)).mpr (by norm_num))

theorem secondJacobianQuarticChart_complement_finite:
    {P:RationalPoints J2 | ¬secondJacobianQuarticChart P}.Finite := by
  apply (Set.toFinite ({0,secondJacobianQuarticBad}:Set (RationalPoints J2))).subset
  intro P hP
  cases P with
  | zero =>
    change (0:RationalPoints J2) ∈ ({0,secondJacobianQuarticBad}:Set (RationalPoints J2))
    simp
  | some x y h =>
    have hN:pointedInverseNum secondQuarticB secondQuarticD secondQuarticQ (secondPointedX x) y=0 := by
      change ¬(pointedInverseNum secondQuarticB secondQuarticD secondQuarticQ (secondPointedX x) y≠0) at hP
      exact not_ne_iff.mp hP
    have hX:=pointed_inverse_num_zero_X secondQuarticA secondQuarticB secondQuarticC secondQuarticD
      secondQuarticQ (secondPointedX x) y secondQuartic_q_ne_zero (secondQuartic_inverse_den_ne_zero x)
      ((secondJacobian_pointed_equation x y).mp ((secondJacobian_equation_iff x y).mp h.1)) hN
    norm_num [secondPointedX,secondQuarticD,secondQuarticC,secondQuarticQ] at hX
    have hx:x=5450739286869/100 := by linarith
    have hy:y=1223344450581962247/1000 := by
      rw [hx] at hN
      norm_num [pointedInverseNum,pointedInverseLinear,secondQuarticB,secondQuarticD,
        secondQuarticQ,secondPointedX] at hN
      linarith
    subst x
    subst y
    simp [secondJacobianQuarticBad,WeierstrassCurve.Affine.Point.mk]

theorem infinite_SecondJacobianQuarticChart [Infinite (RationalPoints J2)]:
    Infinite SecondJacobianQuarticChart := by
  have hi:{P:RationalPoints J2 | secondJacobianQuarticChart P}.Infinite :=
    Set.infinite_of_finite_compl secondJacobianQuarticChart_complement_finite
  exact hi.to_subtype

theorem infinite_SecondQuarticPoint(hSilvermanVII34:OddPrimeTorsionIntegrality):
    Infinite SecondQuarticPoint := by
  let : Infinite (RationalPoints J2) := secondJacobian_infinite hSilvermanVII34
  let : Infinite SecondJacobianQuarticChart := infinite_SecondJacobianQuarticChart
  exact Infinite.of_injective secondJacobianToQuartic secondJacobianToQuartic_injective

end Z2Z4Rank6
