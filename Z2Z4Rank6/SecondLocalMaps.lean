module

public import Z2Z4Rank6.SecondQuarticG2
public import Mathlib.Topology.Algebra.Field

@[expose] public section

/-!
# Continuous coordinates at the printed second-family center

The explicit J2-to-quartic maps are natural over characteristic-zero fields
and continuous at the point corresponding to θ=857/140. This is the
coordinate input to Remark 8.2, separate from its valuation calculation.
-/
namespace Z2Z4Rank6

section Field
variable {K:Type*}[Field K]

def secondJacobianCoordinatesC0 : K×K :=
  (54556950135745026/1371241,-7041812489022755389869000/1605723211)

def secondJacobianCoordinatesToQuartic (z:K×K):K×K :=
  (secondQuarticTheta z.1 z.2,secondQuarticEta z.1 z.2)

variable [CharZero K]

theorem secondCoordinatesC0_theta :
    secondQuarticTheta (secondJacobianCoordinatesC0 (K:=K)).1
      (secondJacobianCoordinatesC0 (K:=K)).2=857/140 := by
  norm_num [secondQuarticTheta,secondQuarticT,pointedInverseT,pointedInverseNum,
    pointedInverseLinear,pointedInverseDen,secondQuarticA,secondQuarticB,secondQuarticD,
    secondQuarticQ,secondPointedX,secondJacobianCoordinatesC0]

theorem secondCoordinatesC0_eta :
    secondQuarticEta (secondJacobianCoordinatesC0 (K:=K)).1
      (secondJacobianCoordinatesC0 (K:=K)).2=103737321/392 := by
  norm_num [secondQuarticEta,secondQuarticT,pointedInverseEta,pointedInverseT,
    pointedInverseNum,pointedInverseLinear,pointedInverseDen,secondQuarticA,secondQuarticB,
    secondQuarticD,secondQuarticQ,secondPointedX,secondJacobianCoordinatesC0]

theorem secondCoordinatesC0_equation :
    (secondJacobianCoordinatesC0 (K:=K)).2^2=
      ((secondJacobianCoordinatesC0 (K:=K)).1+102809641014)*
      ((secondJacobianCoordinatesC0 (K:=K)).1-51068871386)*
      ((secondJacobianCoordinatesC0 (K:=K)).1-51740769627) := by
  norm_num [secondJacobianCoordinatesC0]

theorem secondCoordinatesC0_denom_ne_zero :
    pointedInverseDen secondQuarticA secondQuarticQ
      (secondPointedX (secondJacobianCoordinatesC0 (K:=K)).1)≠0 := by
  norm_num [pointedInverseDen,secondQuarticA,secondQuarticQ,secondPointedX,
    secondJacobianCoordinatesC0]

theorem secondCoordinatesC0_num_ne_zero :
    pointedInverseNum secondQuarticB secondQuarticD secondQuarticQ
      (secondPointedX (secondJacobianCoordinatesC0 (K:=K)).1)
      (secondJacobianCoordinatesC0 (K:=K)).2≠0 := by
  norm_num [pointedInverseNum,pointedInverseLinear,secondQuarticB,secondQuarticD,
    secondQuarticQ,secondPointedX,secondJacobianCoordinatesC0]

end Field

section Naturality
variable {K L:Type*}[Field K][Field L](f:K→+*L)

theorem map_secondQuarticTheta (x y:K):
    f (secondQuarticTheta x y)=secondQuarticTheta (f x) (f y) := by
  simp [secondQuarticTheta,secondQuarticT,pointedInverseT,pointedInverseNum,
    pointedInverseLinear,pointedInverseDen,secondQuarticA,secondQuarticB,secondQuarticD,
    secondQuarticQ,secondPointedX,map_ofNat]

theorem map_secondQuarticEta (x y:K):
    f (secondQuarticEta x y)=secondQuarticEta (f x) (f y) := by
  simp [secondQuarticEta,pointedInverseEta,pointedInverseT,pointedInverseNum,
    pointedInverseLinear,pointedInverseDen,secondQuarticA,secondQuarticB,secondQuarticD,
    secondQuarticQ,secondPointedX,map_ofNat]

theorem map_secondCoordinatesC0:
    Prod.map f f (secondJacobianCoordinatesC0 (K:=K))=secondJacobianCoordinatesC0 (K:=L) := by
  simp [secondJacobianCoordinatesC0,map_ofNat]

end Naturality

section Continuity
variable {K:Type*}[Field K][CharZero K][TopologicalSpace K]
  [IsTopologicalRing K][ContinuousInv₀ K]

omit [CharZero K] in
theorem secondQuarticT_continuousAt (z:K×K)
    (hA:pointedInverseDen secondQuarticA secondQuarticQ (secondPointedX z.1)≠0):
    ContinuousAt (fun w:K×K=>secondQuarticT w.1 w.2) z := by
  unfold secondQuarticT pointedInverseT pointedInverseNum pointedInverseLinear pointedInverseDen secondPointedX
  fun_prop (disch:=exact hA)

omit [CharZero K] in
theorem secondQuarticTheta_continuousAt (z:K×K)
    (hA:pointedInverseDen secondQuarticA secondQuarticQ (secondPointedX z.1)≠0):
    ContinuousAt (fun w:K×K=>secondQuarticTheta w.1 w.2) z := by
  have ht:=secondQuarticT_continuousAt z hA
  unfold secondQuarticTheta
  fun_prop

theorem secondQuarticEta_continuousAt (z:K×K)
    (hA:pointedInverseDen secondQuarticA secondQuarticQ (secondPointedX z.1)≠0):
    ContinuousAt (fun w:K×K=>secondQuarticEta w.1 w.2) z := by
  have ht:=secondQuarticT_continuousAt z hA
  unfold secondQuarticEta pointedInverseEta
  change ContinuousAt (fun w:K×K=>
    (secondPointedX w.1*(secondQuarticT w.1 w.2)^2-
      secondQuarticD*secondQuarticT w.1 w.2-2*secondQuarticQ^2)/(2*secondQuarticQ)) z
  unfold secondPointedX
  fun_prop (disch:=exact mul_ne_zero (by norm_num) secondQuartic_q_ne_zero)

theorem secondCoordinatesToQuartic_continuousAt_c0:
    ContinuousAt (secondJacobianCoordinatesToQuartic (K:=K)) secondJacobianCoordinatesC0 := by
  exact (secondQuarticTheta_continuousAt _ secondCoordinatesC0_denom_ne_zero).prodMk
    (secondQuarticEta_continuousAt _ secondCoordinatesC0_denom_ne_zero)

end Continuity

def secondJacobianC0:RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff (secondJacobianCoordinatesC0 (K:=ℚ)).1
    (secondJacobianCoordinatesC0 (K:=ℚ)).2).mpr secondCoordinatesC0_equation)

theorem secondJacobianC0_in_chart:secondJacobianQuarticChart secondJacobianC0 :=
  secondCoordinatesC0_num_ne_zero

def secondQuarticC0:SecondQuarticPoint where
  theta:=857/140
  eta:=103737321/392
  equation:=by norm_num [secondQuartic]

theorem secondJacobianC0_to_quartic:
    secondJacobianToQuartic ⟨secondJacobianC0,secondJacobianC0_in_chart⟩=secondQuarticC0 := by
  apply SecondQuarticPoint.ext
  · exact secondCoordinatesC0_theta
  · exact secondCoordinatesC0_eta

end Z2Z4Rank6
