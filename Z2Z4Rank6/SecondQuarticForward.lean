import Z2Z4Rank6.SecondQuarticMaps
import Z2Z4Rank6.QuarticBirationalForward

/-!
# Two-sided rational charts for the second quartic and J2

This complements the cofinite inverse used for infinitude. Both
coordinate compositions are checked, without a scheme-level identification.
-/
namespace Z2Z4Rank6
section Field
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem secondQuartic_forward_pointed_X (theta eta : K) :
    secondPointedX (secondQuarticRecoverX theta eta)=
      pointedForwardX secondQuarticD secondQuarticQ (theta-10/3) eta := by
  simp [secondPointedX,secondQuarticRecoverX]

theorem secondQuartic_forward_equation (theta eta : K) (ht : theta-10/3≠0)
    (hE : eta^2=secondQuartic theta) :
    (secondQuarticRecoverY theta eta)^2=
      (secondQuarticRecoverX theta eta+102809641014)*
      (secondQuarticRecoverX theta eta-51068871386)*
      (secondQuarticRecoverX theta eta-51740769627) := by
  apply (secondJacobian_pointed_equation _ _).mpr
  rw [secondQuartic_forward_pointed_X]
  apply pointed_forward_equation _ _ _ _ _ _ _ secondQuartic_q_ne_zero ht
  rw [secondQuartic_shift_identity,sub_add_cancel]
  exact hE

theorem secondQuartic_forward_inverse_Theta (theta eta : K)
    (hA : pointedInverseDen secondQuarticA secondQuarticQ
      (pointedForwardX secondQuarticD secondQuarticQ (theta-10/3) eta)≠0) :
    secondQuarticTheta (secondQuarticRecoverX theta eta) (secondQuarticRecoverY theta eta)=theta := by
  unfold secondQuarticTheta secondQuarticT secondQuarticRecoverY
  rw [secondQuartic_forward_pointed_X]
  rw [pointed_forward_inverse_T _ _ _ _ _ _ secondQuartic_q_ne_zero hA]
  exact sub_add_cancel _ _

theorem secondQuartic_forward_inverse_Eta (theta eta : K) (ht : theta-10/3≠0)
    (hA : pointedInverseDen secondQuarticA secondQuarticQ
      (pointedForwardX secondQuarticD secondQuarticQ (theta-10/3) eta)≠0) :
    secondQuarticEta (secondQuarticRecoverX theta eta) (secondQuarticRecoverY theta eta)=eta := by
  unfold secondQuarticEta
  rw [secondQuartic_forward_pointed_X]
  exact pointed_forward_inverse_eta _ _ _ _ _ _ secondQuartic_q_ne_zero ht hA

end Field

abbrev SecondQuarticRegularPoint := {P : SecondQuarticPoint // P.theta≠10/3}

def secondQuarticToJacobian (P : SecondQuarticRegularPoint) : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff _ _).mpr (secondQuartic_forward_equation P.val.theta P.val.eta
    (sub_ne_zero.mpr P.property) P.val.equation))

theorem secondQuartic_forward_den_ne_zero (P : SecondQuarticPoint) :
    pointedInverseDen secondQuarticA secondQuarticQ
      (pointedForwardX secondQuarticD secondQuarticQ (P.theta-10/3) P.eta)≠0 :=
  pointed_inverse_den_ne_zero _ _ _ secondQuartic_q_ne_zero secondQuartic_leading_nonsquare

theorem secondJacobianToQuartic_regular (P : SecondJacobianQuarticChart) :
    (secondJacobianToQuartic P).theta≠10/3 := by
  rcases P with ⟨P,hP⟩
  cases P with
  | zero => exact hP.elim
  | some x y h =>
    change secondQuarticT x y+10/3≠10/3
    exact add_ne_right.mpr (secondJacobian_chart_T_ne_zero x y hP)

theorem secondQuarticToJacobian_in_chart (P : SecondQuarticRegularPoint) :
    secondJacobianQuarticChart (secondQuarticToJacobian P) := by
  change pointedInverseNum secondQuarticB secondQuarticD secondQuarticQ
    (secondPointedX (secondQuarticRecoverX P.val.theta P.val.eta))
    (secondQuarticRecoverY P.val.theta P.val.eta)≠0
  rw [secondQuartic_forward_pointed_X]
  unfold secondQuarticRecoverY
  have ht := pointed_forward_inverse_T secondQuarticA secondQuarticB secondQuarticD secondQuarticQ
    (P.val.theta-10/3) P.val.eta secondQuartic_q_ne_zero (secondQuartic_forward_den_ne_zero P.val)
  intro hN
  simp only [pointedInverseT,hN,zero_div] at ht
  exact (sub_ne_zero.mpr P.property) ht.symm

def secondQuarticChartEquiv : SecondJacobianQuarticChart ≃ SecondQuarticRegularPoint where
  toFun P := ⟨secondJacobianToQuartic P,secondJacobianToQuartic_regular P⟩
  invFun P := ⟨secondQuarticToJacobian P,secondQuarticToJacobian_in_chart P⟩
  left_inv P := by
    rcases P with ⟨P,hP⟩
    apply Subtype.ext
    cases P with
    | zero => exact hP.elim
    | some x y h =>
      dsimp only [secondQuarticToJacobian,secondJacobianToQuartic]
      simp only [WeierstrassCurve.Affine.Point.mk]
      congr 1
      · exact secondQuartic_recover_X x y (secondJacobian_chart_T_ne_zero x y hP)
      · exact secondQuartic_recover_Y x y (secondQuartic_inverse_den_ne_zero x)
          (secondJacobian_chart_T_ne_zero x y hP)
  right_inv P := by
    apply Subtype.ext
    apply SecondQuarticPoint.ext
    · exact secondQuartic_forward_inverse_Theta P.val.theta P.val.eta (secondQuartic_forward_den_ne_zero P.val)
    · exact secondQuartic_forward_inverse_Eta P.val.theta P.val.eta (sub_ne_zero.mpr P.property)
        (secondQuartic_forward_den_ne_zero P.val)

end Z2Z4Rank6
