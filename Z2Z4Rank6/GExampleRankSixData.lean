module

public import Z2Z4Rank6.TwoDescent
public import Z2Z4Rank6.Torsion
public import Z2Z4Rank6.GReductionData

@[expose] public section

/-!
# Six rational points on the printed genus-one G-fiber example

The abscissae are P₁, P₂, P₃, P₃′ at m=291/53 and the two extra values
printed after Proposition 7.2 of Jaswal, DOI 10.5281/zenodo.23437117.
All ordinates, square factors and descent values are exact kernel certificates.
-/
namespace Z2Z4Rank6.GExampleRankSix

noncomputable section

def A : ℚ := 379291648
def B : ℚ := 212565977
abbrev curve : WeierstrassCurve ℚ := E A B

theorem factor_nonzero : A*B*(A^2-B^2)≠0 := by norm_num [A,B]
instance curveElliptic : curve.IsElliptic := E_good A B factor_nonzero

def xs : Fin 6 → ℚ :=
  ![GReductionData.rationalX 0,GReductionData.rationalX 1,
    GReductionData.rationalX 2,GReductionData.rationalX 4,
    585506734092845056,1093412290152185253846016/17732521]

def ys : Fin 6 → ℚ := ![14249583615419300158832640, 8136347447441088722850120, 606957782636939578644234240/343, 4153473587131885601894400, 518976736853405541941903360, 2747715799335240054670176339232640000/74671645931]

def representatives : Fin 8 → ℚ×ℚ := ![(-1, 165720135), (-79616134, 23365770), (-179632414, 484127970), (-70219, 277221), (1227349, 2782321503965), (13149271, 6771051875303855), (-1, 3947114386583655), (78734863012754, 8769009920610)]

def squareFactors : Fin 8 → ℚ×ℚ := ![(293233408, 18688), (27094, 60462), (111872/7, 99584/7), (834496, 585280), (690688, 512), (288364064/4211, 23200/4211), (379291648, 5/379291648), (32, 160)]

def parityVectors : Fin 8 → Fin 8 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 1, 0],
    ![1, 1, 0, 0, 0, 1, 1, 0],
    ![1, 0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 1, 1, 1, 0]]

theorem point_equation (i : Fin 6) : curve.toAffine.Equation (xs i) (ys i) := by
  change (E A B).toAffine.Equation (xs i) (ys i)
  rw [E_equation_iff]
  fin_cases i <;> norm_num [xs,ys,A,B,GReductionData.rationalX]

def points (i : Fin 6) : RationalPoints curve := .mk (point_equation i)
def two : RationalPoints curve := twoLeft A B factor_nonzero
def four : RationalPoints curve := fourPoint A B factor_nonzero

def eightPoints : Fin 8 → RationalPoints curve :=
  ![points 0,points 1,points 2,points 3,points 4,points 5,two,four]

def rawValues : Fin 8 → ℚ×ℚ :=
  ![(xs 0,xs 0+A^2),(xs 1,xs 1+A^2),(xs 2,xs 2+A^2),
    (xs 3,xs 3+A^2),(xs 4,xs 4+A^2),(xs 5,xs 5+A^2),
    (-A^2,(A^2-B^2)/A^2),(A*B,A*B+A^2)]

/-- All sixteen squareclass identities, including the special two-torsion
coordinate and the printed four-torsion coordinate. -/
theorem square_factors (i : Fin 8) :
    (rawValues i).1=(representatives i).1*(squareFactors i).1^2 ∧
      (rawValues i).2=(representatives i).2*(squareFactors i).2^2 := by
  fin_cases i <;> norm_num [rawValues,representatives,squareFactors,xs,A,B,
    GReductionData.rationalX]

noncomputable def squareclasses : Fin 8 → RatSquareClassAdd×RatSquareClassAdd :=
  fun i => (squareClass (representatives i).1,squareClass (representatives i).2)

theorem raw_squareclasses (i : Fin 8) :
    (squareClass (rawValues i).1,squareClass (rawValues i).2)=squareclasses i := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (squareFactors i).1
    · fin_cases i <;> norm_num [rawValues,xs,A,B,GReductionData.rationalX]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (square_factors i).1
  · apply squareClass_eq_of_factor _ _ (squareFactors i).2
    · fin_cases i <;> norm_num [rawValues,xs,A,B,GReductionData.rationalX]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (square_factors i).2

/-- Complete-descent coordinates of all eight rational points. -/
theorem descent_coordinates (i : Fin 8) :
    completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (eightPoints i)=squareclasses i := by
  rw [←raw_squareclasses i]
  fin_cases i <;> norm_num [eightPoints,points,two,four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,rawValues,xs,ys,A,B,
    GReductionData.rationalX]

end
end Z2Z4Rank6.GExampleRankSix
