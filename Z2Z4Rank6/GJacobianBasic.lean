module

public import Z2Z4Rank6.Torsion
public import Z2Z4Rank6.TwoDescent

@[expose] public section

/-!
# The Jacobian equation printed for G

Equation, point coordinates, and root translation in Jaswal, Proposition 7.2(a),
DOI 10.5281/zenodo.23437117. The quartic G's geometric identification with
this equation is separate; the present file constructs its point group.
-/
namespace Z2Z4Rank6
open WeierstrassCurve Affine Affine.Point

def JG : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := -26097400
  a₆ := 38851416548

theorem gJacobian_discriminant : JG.Δ = (16*9801^2*2401^2*7400^2 : ℚ) := by
  norm_num [JG,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance gJacobian_isElliptic : JG.IsElliptic where
  isUnit := by rw [isUnit_iff_ne_zero,gJacobian_discriminant]; norm_num

instance gJacobianSplit_isElliptic : (E (99 : ℚ) 49).IsElliptic :=
  E_good 99 49 (by norm_num)

theorem gJacobian_equation_iff (x y : ℚ) :
    JG.toAffine.Equation x y ↔ y^2=(x+5734)*(x-1666)*(x-4067) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [JG,zero_mul,add_zero]
  constructor <;> intro h <;> linear_combination h

theorem gJacobian_split_equation (x y : ℚ) :
    JG.toAffine.Equation x y ↔ (E (99 : ℚ) 49).toAffine.Equation (x-4067) y := by
  rw [gJacobian_equation_iff, E_equation_iff]
  ring_nf

def gJacobianToSplit : RationalPoints JG → RationalPoints (E (99 : ℚ) 49)
  | .zero => 0
  | .some x y h => .mk ((gJacobian_split_equation x y).mp h.1)

def splitToGJacobian : RationalPoints (E (99 : ℚ) 49) → RationalPoints JG
  | .zero => 0
  | .some x y h => .mk ((gJacobian_split_equation (x+4067) y).mpr (by simpa using h.1))

theorem gJacobianToSplit_left_inverse : Function.LeftInverse splitToGJacobian gJacobianToSplit := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp [gJacobianToSplit, splitToGJacobian, Point.mk]

theorem gJacobianToSplit_right_inverse : Function.RightInverse splitToGJacobian gJacobianToSplit := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp [gJacobianToSplit, splitToGJacobian, Point.mk]

theorem gJacobian_split_slope (x1 x2 y1 y2 : ℚ) :
    (E (99 : ℚ) 49).toAffine.slope (x1-4067) (x2-4067) y1 y2 =
      JG.toAffine.slope x1 x2 y1 y2 := by
  simp only [slope, negY, E, JG, zero_mul, sub_zero, sub_left_inj]
  split_ifs <;> ring

theorem gJacobian_split_addX (x1 x2 l : ℚ) :
    (E (99 : ℚ) 49).toAffine.addX (x1-4067) (x2-4067) l =
      JG.toAffine.addX x1 x2 l - 4067 := by
  unfold addX
  simp only [E, JG]
  ring

theorem gJacobian_split_addY (x1 x2 y1 l : ℚ) :
    (E (99 : ℚ) 49).toAffine.addY (x1-4067) (x2-4067) y1 l =
      JG.toAffine.addY x1 x2 y1 l := by
  unfold addY negAddY addX negY
  simp only [E, JG]
  ring

theorem gJacobianToSplit_add (P Q : RationalPoints JG) :
    gJacobianToSplit (P+Q) = gJacobianToSplit P + gJacobianToSplit Q := by
  cases P with
  | zero => rfl
  | some x1 y1 h1 =>
    cases Q with
    | zero =>
      change gJacobianToSplit ((Point.some x1 y1 h1) + 0) = gJacobianToSplit (.some x1 y1 h1) + 0
      rw [add_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hv : x1 = x2 ∧ y1 = -y2
      · rw [Point.add_of_Y_eq hv.1 (by simpa [JG, negY] using hv.2)]
        simp only [gJacobianToSplit, Point.mk]
        exact (Point.add_of_Y_eq (by rw [hv.1]) (by simpa [E, negY] using hv.2)).symm
      · rw [Point.add_some (by simpa [JG, negY] using hv)]
        simp only [gJacobianToSplit, Point.mk]
        rw [Point.add_some (by simpa [E, negY, sub_left_inj] using hv)]
        congr 1
        · rw [gJacobian_split_slope, gJacobian_split_addX]
        · rw [gJacobian_split_slope, gJacobian_split_addY]

def gJacobianSplitEquiv : RationalPoints JG ≃+ RationalPoints (E (99 : ℚ) 49) where
  toFun := gJacobianToSplit
  invFun := splitToGJacobian
  left_inv := gJacobianToSplit_left_inverse
  right_inv := gJacobianToSplit_right_inverse
  map_add' := gJacobianToSplit_add

def gJacobianP1 : RationalPoints JG :=
  .mk ((gJacobian_equation_iff (-5194) 185220).mpr (by norm_num))
def gJacobianP2 : RationalPoints JG :=
  .mk ((gJacobian_equation_iff (-4249) 270270).mpr (by norm_num))
def gJacobianFour : RationalPoints JG :=
  .mk ((gJacobian_equation_iff (-784) 242550).mpr (by norm_num))
def gJacobianTwo : RationalPoints JG :=
  .mk ((gJacobian_equation_iff 1666 0).mpr (by norm_num))
def gJacobianDoubleFour : RationalPoints JG :=
  .mk ((gJacobian_equation_iff 4067 0).mpr (by norm_num))

def gJacobianPoints : Fin 2 → RationalPoints JG := ![gJacobianP1,gJacobianP2]
def gJacobianFourPoints : Fin 4 → RationalPoints JG :=
  ![gJacobianP1,gJacobianP2,gJacobianFour,gJacobianTwo]

end Z2Z4Rank6
