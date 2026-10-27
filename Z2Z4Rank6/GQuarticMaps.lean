module

public import Z2Z4Rank6.QuarticBirational
public import Z2Z4Rank6.GJacobianInfinite

@[expose] public section

/-!
# Rational maps from the Jacobian printed for G to the printed quartic G

The cubic produced from the rational quartic point (57,31836) differs
from the printed JG equation only by X=4x−639968,Y=8y. Source: Jaswal Proposition 7.2(a), DOI
10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6
section Field
variable {K:Type*}[Field K]

def gQuartic (t:K):K :=99*t^4-9998*t^2+970299
def gQuarticA : K :=99
def gQuarticB : K :=22572
def gQuarticC : K :=1919908
def gQuarticD : K :=72196656
def gQuarticQ : K :=31836
def gPointedX (x:K):K :=4*x-639968
def gPointedY (y:K):K :=8*y
def gQuarticT (x y:K):K :=
  pointedInverseT gQuarticA gQuarticB gQuarticD gQuarticQ (gPointedX x) (gPointedY y)
def gQuarticM (x y:K):K :=gQuarticT x y+57
def gQuarticEta (x y:K):K :=
  pointedInverseEta gQuarticA gQuarticB gQuarticD gQuarticQ (gPointedX x) (gPointedY y)
def gQuarticRecoverX (m eta:K):K :=
  (pointedForwardX gQuarticD gQuarticQ (m-57) eta+639968)/4
def gQuarticRecoverY (m eta:K):K :=
  pointedForwardY gQuarticA gQuarticB gQuarticD gQuarticQ (m-57) eta/8

variable [CharZero K]

theorem gQuartic_q_ne_zero : (gQuarticQ:K)≠0 := by norm_num [gQuarticQ]

omit [CharZero K] in
theorem gQuartic_shift_identity (t:K):
    pointedQuartic gQuarticA gQuarticB gQuarticC gQuarticD gQuarticQ t=
      gQuartic (t+57) := by
  norm_num [pointedQuartic,gQuartic,gQuarticA,gQuarticB,gQuarticC,
    gQuarticD,gQuarticQ]
  ring

theorem gJacobian_pointed_equation (x y:K):
    y^2=(x+5734)*(x-1666)*(x-4067) ↔
      (gPointedY y)^2=pointedCubic gQuarticA gQuarticB gQuarticC gQuarticD gQuarticQ
        (gPointedX x) := by
  have he:pointedCubic gQuarticA gQuarticB gQuarticC gQuarticD gQuarticQ
      (gPointedX x)=64*((x+5734)*(x-1666)*(x-4067)) := by
    norm_num [pointedCubic,gQuarticA,gQuarticB,gQuarticC,gQuarticD,gQuarticQ,gPointedX]
    ring
  rw [he]
  unfold gPointedY
  constructor
  · intro h
    linear_combination 64*h
  · intro h
    linear_combination (1/64:K)*h

theorem gQuartic_coordinates_equation (x y:K)
    (hE:y^2=(x+5734)*(x-1666)*(x-4067))
    (hA:pointedInverseDen gQuarticA gQuarticQ (gPointedX x)≠0):
    (gQuarticEta x y)^2=gQuartic (gQuarticM x y) := by
  have hi:=pointed_inverse_equation gQuarticA gQuarticB gQuarticC gQuarticD
    gQuarticQ (gPointedX x) (gPointedY y) gQuartic_q_ne_zero hA
    ((gJacobian_pointed_equation x y).mp hE)
  rw [gQuartic_shift_identity] at hi
  exact hi

theorem gQuartic_recover_X (x y:K)
    (ht:gQuarticT x y≠0):
    gQuarticRecoverX (gQuarticM x y) (gQuarticEta x y)=x := by
  simp only [gQuarticRecoverX,gQuarticM,add_sub_cancel_right,gQuarticEta]
  simp only [gQuarticT] at ht ⊢
  rw [pointed_inverse_forward_X _ _ _ _ _ _ gQuartic_q_ne_zero ht]
  norm_num [gPointedX]

theorem gQuartic_recover_Y (x y:K)
    (hA:pointedInverseDen gQuarticA gQuarticQ (gPointedX x)≠0)
    (ht:gQuarticT x y≠0):
    gQuarticRecoverY (gQuarticM x y) (gQuarticEta x y)=y := by
  simp only [gQuarticRecoverY,gQuarticM,add_sub_cancel_right,gQuarticEta]
  simp only [gQuarticT] at ht ⊢
  rw [pointed_inverse_forward_Y _ _ _ _ _ _ gQuartic_q_ne_zero hA ht]
  norm_num [gPointedY]

end Field

theorem gQuartic_leading_nonsquare : ¬IsSquare (gQuarticA:ℚ) := by
  norm_num [gQuarticA]

theorem gQuartic_inverse_den_ne_zero (x:ℚ):
    pointedInverseDen gQuarticA gQuarticQ (gPointedX x)≠0 :=
  pointed_inverse_den_ne_zero _ _ _ gQuartic_q_ne_zero gQuartic_leading_nonsquare

@[ext] structure GQuarticPoint where
  m : ℚ
  eta : ℚ
  equation : eta^2=gQuartic m

def gJacobianQuarticChart : RationalPoints JG→Prop
  | .zero => False
  | .some x y _ => pointedInverseNum gQuarticB gQuarticD gQuarticQ (gPointedX x) (gPointedY y)≠0

abbrev GJacobianQuarticChart := {P:RationalPoints JG // gJacobianQuarticChart P}

def gJacobianToQuartic (P:GJacobianQuarticChart):GQuarticPoint := by
  rcases P with ⟨P,hP⟩
  cases P with
  | zero => exact hP.elim
  | some x y h => exact ⟨gQuarticM x y,gQuarticEta x y,
      gQuartic_coordinates_equation x y ((gJacobian_equation_iff x y).mp h.1)
        (gQuartic_inverse_den_ne_zero x)⟩

theorem gJacobian_chart_T_ne_zero (x y:ℚ)
    (h:pointedInverseNum gQuarticB gQuarticD gQuarticQ (gPointedX x) (gPointedY y)≠0):
    gQuarticT x y≠0 :=
  div_ne_zero h (gQuartic_inverse_den_ne_zero x)

theorem gJacobianToQuartic_injective:Function.Injective gJacobianToQuartic := by
  rintro ⟨P,hP⟩ ⟨Q,hQ⟩ heq
  apply Subtype.ext
  cases P with
  | zero => exact hP.elim
  | some x1 y1 hp =>
    cases Q with
    | zero => exact hQ.elim
    | some x2 y2 hq =>
      have ht1:=gJacobian_chart_T_ne_zero x1 y1 hP
      have ht2:=gJacobian_chart_T_ne_zero x2 y2 hQ
      have hx:=congrArg (fun z:GQuarticPoint=>gQuarticRecoverX z.m z.eta) heq
      have hy:=congrArg (fun z:GQuarticPoint=>gQuarticRecoverY z.m z.eta) heq
      change gQuarticRecoverX (gQuarticM x1 y1) (gQuarticEta x1 y1)=
        gQuarticRecoverX (gQuarticM x2 y2) (gQuarticEta x2 y2) at hx
      change gQuarticRecoverY (gQuarticM x1 y1) (gQuarticEta x1 y1)=
        gQuarticRecoverY (gQuarticM x2 y2) (gQuarticEta x2 y2) at hy
      rw [gQuartic_recover_X x1 y1 ht1,gQuartic_recover_X x2 y2 ht2] at hx
      rw [gQuartic_recover_Y x1 y1 (gQuartic_inverse_den_ne_zero x1) ht1,
        gQuartic_recover_Y x2 y2 (gQuartic_inverse_den_ne_zero x2) ht2] at hy
      cases hx
      cases hy
      rfl

def gJacobianQuarticBad : RationalPoints JG :=
  .mk ((gJacobian_equation_iff (206581256/143641)
    (3567977201250/54439939)).mpr (by norm_num))

theorem gJacobianQuarticChart_complement_finite:
    {P:RationalPoints JG | ¬gJacobianQuarticChart P}.Finite := by
  apply (Set.toFinite ({0,gJacobianQuarticBad}:Set (RationalPoints JG))).subset
  intro P hP
  cases P with
  | zero =>
    change (0:RationalPoints JG) ∈ ({0,gJacobianQuarticBad}:Set (RationalPoints JG))
    simp
  | some x y h =>
    have hN:pointedInverseNum gQuarticB gQuarticD gQuarticQ (gPointedX x) (gPointedY y)=0 := by
      change ¬(pointedInverseNum gQuarticB gQuarticD gQuarticQ (gPointedX x) (gPointedY y)≠0) at hP
      exact not_ne_iff.mp hP
    have hX:=pointed_inverse_num_zero_X gQuarticA gQuarticB gQuarticC gQuarticD
      gQuarticQ (gPointedX x) (gPointedY y) gQuartic_q_ne_zero (gQuartic_inverse_den_ne_zero x)
      ((gJacobian_pointed_equation x y).mp ((gJacobian_equation_iff x y).mp h.1)) hN
    norm_num [gPointedX,gQuarticD,gQuarticC,gQuarticQ] at hX
    have hx:x=206581256/143641 := by linarith
    have hy:y=3567977201250/54439939 := by
      rw [hx] at hN
      norm_num [pointedInverseNum,pointedInverseLinear,gQuarticB,gQuarticD,
        gQuarticQ,gPointedX,gPointedY] at hN
      linarith
    subst x
    subst y
    simp [gJacobianQuarticBad,WeierstrassCurve.Affine.Point.mk]

theorem infinite_GJacobianQuarticChart [Infinite (RationalPoints JG)]:
    Infinite GJacobianQuarticChart := by
  have hi:{P:RationalPoints JG | gJacobianQuarticChart P}.Infinite :=
    Set.infinite_of_finite_compl gJacobianQuarticChart_complement_finite
  exact hi.to_subtype

theorem infinite_GQuarticPoint(hSilvermanVII34:OddPrimeTorsionIntegrality):
    Infinite GQuarticPoint := by
  let : Infinite (RationalPoints JG) := gJacobian_infinite hSilvermanVII34
  let : Infinite GJacobianQuarticChart := infinite_GJacobianQuarticChart
  exact Infinite.of_injective gJacobianToQuartic gJacobianToQuartic_injective

end Z2Z4Rank6
