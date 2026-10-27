import Z2Z4Rank6.Torsion
import Z2Z4Rank6.TwoDescent

/-!
# The Jacobian equation printed for G2

Equation, point coordinates, and root translation in Jaswal, Theorem 8.1(a),
DOI 10.5281/zenodo.23437117. The quartic G2's geometric identification with
this equation is separate; the present file constructs its point group.
-/
namespace Z2Z4Rank6
open WeierstrassCurve Affine Affine.Point

def J2 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := -7927479575830823114160
  a₆ := 271658305399029819040875379804308

theorem secondJacobian_discriminant : J2.Δ = (16*154550410641^2*671898241^2*153878512400^2 : ℚ) := by
  norm_num [J2,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance secondJacobian_isElliptic : J2.IsElliptic where
  isUnit := by rw [isUnit_iff_ne_zero,secondJacobian_discriminant]; norm_num

instance secondJacobianSplit_isElliptic : (E (393129 : ℚ) 25921).IsElliptic :=
  E_good 393129 25921 (by norm_num)

theorem secondJacobian_equation_iff (x y : ℚ) :
    J2.toAffine.Equation x y ↔ y^2=(x+102809641014)*(x-51068871386)*(x-51740769627) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [J2,zero_mul,add_zero]
  constructor <;> intro h <;> linear_combination h

theorem secondJacobian_split_equation (x y : ℚ) :
    J2.toAffine.Equation x y ↔ (E (393129 : ℚ) 25921).toAffine.Equation (x-51740769627) y := by
  rw [secondJacobian_equation_iff, E_equation_iff]
  ring_nf

def secondJacobianToSplit : RationalPoints J2 → RationalPoints (E (393129 : ℚ) 25921)
  | .zero => 0
  | .some x y h => .mk ((secondJacobian_split_equation x y).mp h.1)

def splitToSecondJacobian : RationalPoints (E (393129 : ℚ) 25921) → RationalPoints J2
  | .zero => 0
  | .some x y h => .mk ((secondJacobian_split_equation (x+51740769627) y).mpr (by simpa using h.1))

theorem secondJacobianToSplit_left_inverse : Function.LeftInverse splitToSecondJacobian secondJacobianToSplit := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp [secondJacobianToSplit, splitToSecondJacobian, Point.mk]

theorem secondJacobianToSplit_right_inverse : Function.RightInverse splitToSecondJacobian secondJacobianToSplit := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp [secondJacobianToSplit, splitToSecondJacobian, Point.mk]

theorem secondJacobian_split_slope (x1 x2 y1 y2 : ℚ) :
    (E (393129 : ℚ) 25921).toAffine.slope (x1-51740769627) (x2-51740769627) y1 y2 =
      J2.toAffine.slope x1 x2 y1 y2 := by
  simp only [slope, negY, E, J2, zero_mul, sub_zero, sub_left_inj]
  split_ifs <;> ring

theorem secondJacobian_split_addX (x1 x2 l : ℚ) :
    (E (393129 : ℚ) 25921).toAffine.addX (x1-51740769627) (x2-51740769627) l =
      J2.toAffine.addX x1 x2 l - 51740769627 := by
  unfold addX
  simp only [E, J2]
  ring

theorem secondJacobian_split_addY (x1 x2 y1 l : ℚ) :
    (E (393129 : ℚ) 25921).toAffine.addY (x1-51740769627) (x2-51740769627) y1 l =
      J2.toAffine.addY x1 x2 y1 l := by
  unfold addY negAddY addX negY
  simp only [E, J2]
  ring

theorem secondJacobianToSplit_add (P Q : RationalPoints J2) :
    secondJacobianToSplit (P+Q) = secondJacobianToSplit P + secondJacobianToSplit Q := by
  cases P with
  | zero => rfl
  | some x1 y1 h1 =>
    cases Q with
    | zero =>
      change secondJacobianToSplit ((Point.some x1 y1 h1) + 0) = secondJacobianToSplit (.some x1 y1 h1) + 0
      rw [add_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hv : x1 = x2 ∧ y1 = -y2
      · rw [Point.add_of_Y_eq hv.1 (by simpa [J2, negY] using hv.2)]
        simp only [secondJacobianToSplit, Point.mk]
        exact (Point.add_of_Y_eq (by rw [hv.1]) (by simpa [E, negY] using hv.2)).symm
      · rw [Point.add_some (by simpa [J2, negY] using hv)]
        simp only [secondJacobianToSplit, Point.mk]
        rw [Point.add_some (by simpa [E, negY, sub_left_inj] using hv)]
        congr 1
        · rw [secondJacobian_split_slope, secondJacobian_split_addX]
        · rw [secondJacobian_split_slope, secondJacobian_split_addY]

def secondJacobianSplitEquiv : RationalPoints J2 ≃+ RationalPoints (E (393129 : ℚ) 25921) where
  toFun := secondJacobianToSplit
  invFun := splitToSecondJacobian
  left_inv := secondJacobianToSplit_left_inverse
  right_inv := secondJacobianToSplit_right_inverse
  map_add' := secondJacobianToSplit_add

def secondJacobianP1 : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff 50796866898 198589582959768).mpr (by norm_num))
def secondJacobianP2 : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff (389256165869/4) (164296202311285275/8)).mpr (by norm_num))
def secondJacobianFour : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff 41550472818 3741958510639272).mpr (by norm_num))
def secondJacobianTwo : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff 51068871386 0).mpr (by norm_num))
def secondJacobianDoubleFour : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff 51740769627 0).mpr (by norm_num))

def secondJacobianPoints : Fin 2 → RationalPoints J2 := ![secondJacobianP1,secondJacobianP2]
def secondJacobianFourPoints : Fin 4 → RationalPoints J2 :=
  ![secondJacobianP1,secondJacobianP2,secondJacobianFour,secondJacobianTwo]

end Z2Z4Rank6
