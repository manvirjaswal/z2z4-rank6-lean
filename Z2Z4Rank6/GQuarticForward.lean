import Z2Z4Rank6.GQuarticMaps
import Z2Z4Rank6.QuarticBirationalForward

/-!
# Both directions of the G/JG rational maps

The forward coordinates and both compositions are checked directly on their
rational charts. This is a statement about equation solutions; the scheme-level genus/Jacobian
clauses of Proposition 7.2(a) are separate.
-/
namespace Z2Z4Rank6
section Field
variable {K : Type*} [Field K] [CharZero K]

theorem gQuartic_forward_pointed_X (m eta : K) :
    gPointedX (gQuarticRecoverX m eta)=pointedForwardX gQuarticD gQuarticQ (m-57) eta := by
  unfold gPointedX gQuarticRecoverX
  field_simp
  ring

theorem gQuartic_forward_pointed_Y (m eta : K) :
    gPointedY (gQuarticRecoverY m eta)=pointedForwardY gQuarticA gQuarticB gQuarticD gQuarticQ (m-57) eta := by
  unfold gPointedY gQuarticRecoverY
  field_simp

theorem gQuartic_forward_equation (m eta : K) (ht : m-57≠0)
    (hE : eta^2=gQuartic m) :
    (gQuarticRecoverY m eta)^2=
      (gQuarticRecoverX m eta+5734)*(gQuarticRecoverX m eta-1666)*
        (gQuarticRecoverX m eta-4067) := by
  apply (gJacobian_pointed_equation _ _).mpr
  rw [gQuartic_forward_pointed_X,gQuartic_forward_pointed_Y]
  apply pointed_forward_equation _ _ _ _ _ _ _ gQuartic_q_ne_zero ht
  rw [gQuartic_shift_identity,sub_add_cancel]
  exact hE

theorem gQuartic_forward_inverse_M (m eta : K)
    (hA : pointedInverseDen gQuarticA gQuarticQ
      (pointedForwardX gQuarticD gQuarticQ (m-57) eta)≠0) :
    gQuarticM (gQuarticRecoverX m eta) (gQuarticRecoverY m eta)=m := by
  unfold gQuarticM gQuarticT
  rw [gQuartic_forward_pointed_X,gQuartic_forward_pointed_Y]
  rw [pointed_forward_inverse_T _ _ _ _ _ _ gQuartic_q_ne_zero hA]
  exact sub_add_cancel _ _

theorem gQuartic_forward_inverse_Eta (m eta : K) (ht : m-57≠0)
    (hA : pointedInverseDen gQuarticA gQuarticQ
      (pointedForwardX gQuarticD gQuarticQ (m-57) eta)≠0) :
    gQuarticEta (gQuarticRecoverX m eta) (gQuarticRecoverY m eta)=eta := by
  unfold gQuarticEta
  rw [gQuartic_forward_pointed_X,gQuartic_forward_pointed_Y]
  exact pointed_forward_inverse_eta _ _ _ _ _ _ gQuartic_q_ne_zero ht hA

end Field

abbrev GQuarticRegularPoint := {P : GQuarticPoint // P.m≠57}

def gQuarticToJacobian (P : GQuarticRegularPoint) : RationalPoints JG :=
  .mk ((gJacobian_equation_iff _ _).mpr (gQuartic_forward_equation P.val.m P.val.eta
    (sub_ne_zero.mpr P.property) P.val.equation))

theorem gQuartic_forward_den_ne_zero (P : GQuarticPoint) :
    pointedInverseDen gQuarticA gQuarticQ
      (pointedForwardX gQuarticD gQuarticQ (P.m-57) P.eta)≠0 :=
  pointed_inverse_den_ne_zero _ _ _ gQuartic_q_ne_zero gQuartic_leading_nonsquare

theorem gQuarticToJacobian_injective : Function.Injective gQuarticToJacobian := by
  intro P Q h
  have hc := WeierstrassCurve.Affine.Point.some.inj h
  have hm := congrArg₂ gQuarticM hc.1 hc.2
  have he := congrArg₂ gQuarticEta hc.1 hc.2
  rw [gQuartic_forward_inverse_M _ _ (gQuartic_forward_den_ne_zero P.val),
    gQuartic_forward_inverse_M _ _ (gQuartic_forward_den_ne_zero Q.val)] at hm
  rw [gQuartic_forward_inverse_Eta _ _ (sub_ne_zero.mpr P.property) (gQuartic_forward_den_ne_zero P.val),
    gQuartic_forward_inverse_Eta _ _ (sub_ne_zero.mpr Q.property) (gQuartic_forward_den_ne_zero Q.val)] at he
  exact Subtype.ext (GQuarticPoint.ext hm he)

theorem gJacobianToQuartic_regular (P : GJacobianQuarticChart) :
    (gJacobianToQuartic P).m≠57 := by
  rcases P with ⟨P,hP⟩
  cases P with
  | zero => exact hP.elim
  | some x y h =>
    change gQuarticT x y+57≠57
    exact add_ne_right.mpr (gJacobian_chart_T_ne_zero x y hP)

theorem gQuarticToJacobian_in_chart (P : GQuarticRegularPoint) :
    gJacobianQuarticChart (gQuarticToJacobian P) := by
  change pointedInverseNum gQuarticB gQuarticD gQuarticQ
    (gPointedX (gQuarticRecoverX P.val.m P.val.eta))
    (gPointedY (gQuarticRecoverY P.val.m P.val.eta))≠0
  rw [gQuartic_forward_pointed_X,gQuartic_forward_pointed_Y]
  have ht := pointed_forward_inverse_T gQuarticA gQuarticB gQuarticD gQuarticQ
    (P.val.m-57) P.val.eta gQuartic_q_ne_zero (gQuartic_forward_den_ne_zero P.val)
  intro hN
  simp only [pointedInverseT,hN,zero_div] at ht
  exact (sub_ne_zero.mpr P.property) ht.symm

def gQuarticChartEquiv : GJacobianQuarticChart ≃ GQuarticRegularPoint where
  toFun P := ⟨gJacobianToQuartic P,gJacobianToQuartic_regular P⟩
  invFun P := ⟨gQuarticToJacobian P,gQuarticToJacobian_in_chart P⟩
  left_inv P := by
    rcases P with ⟨P,hP⟩
    apply Subtype.ext
    cases P with
    | zero => exact hP.elim
    | some x y h =>
      dsimp only [gQuarticToJacobian,gJacobianToQuartic]
      simp only [WeierstrassCurve.Affine.Point.mk]
      congr 1
      · exact gQuartic_recover_X x y (gJacobian_chart_T_ne_zero x y hP)
      · exact gQuartic_recover_Y x y (gQuartic_inverse_den_ne_zero x)
          (gJacobian_chart_T_ne_zero x y hP)
  right_inv P := by
    apply Subtype.ext
    apply GQuarticPoint.ext
    · exact gQuartic_forward_inverse_M P.val.m P.val.eta (gQuartic_forward_den_ne_zero P.val)
    · exact gQuartic_forward_inverse_Eta P.val.m P.val.eta (sub_ne_zero.mpr P.property)
        (gQuartic_forward_den_ne_zero P.val)

def gQuarticAt57 : Bool → GQuarticPoint
  | false => ⟨57,31836,by norm_num [gQuartic]⟩
  | true => ⟨57,-31836,by norm_num [gQuartic]⟩

theorem gQuarticRegularChart_complement_finite :
    {P : GQuarticPoint | ¬P.m≠57}.Finite := by
  apply (Set.finite_range gQuarticAt57).subset
  intro P hP
  have hm : P.m=57 := not_ne_iff.mp hP
  have hE := P.equation
  rw [hm] at hE
  norm_num [gQuartic] at hE
  have he : (P.eta-31836)*(P.eta+31836)=0 := by nlinarith
  rcases mul_eq_zero.mp he with he | he
  · refine ⟨false,?_⟩
    apply GQuarticPoint.ext
    · exact hm.symm
    · change 31836=P.eta
      linarith
  · refine ⟨true,?_⟩
    apply GQuarticPoint.ext
    · exact hm.symm
    · change -31836=P.eta
      linarith

end Z2Z4Rank6
