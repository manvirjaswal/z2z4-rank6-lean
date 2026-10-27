import Z2Z4Rank6.GJacobianBasic
import Z2Z4Rank6.GJacobianVector

/-! Both the printed root-order Kummer values and the translated
complete-descent coordinates for J_G, Proposition 7.2(a). -/
namespace Z2Z4Rank6

def gJacobianRawValues : Fin 4 → ℚ×ℚ :=
  ![(-9261,540),(-8316,1485),(-4851,4950),(-2401,7400)]
def gJacobianCoordinateFactors : Fin 4 → ℚ×ℚ := ![(21,6),(6,3),(21,15),(49,10)]

theorem gJacobian_coordinate_factors(i:Fin 4):
    (gJacobianRawValues i).1=(gJacobianRepresentatives i).1*(gJacobianCoordinateFactors i).1^2 ∧
    (gJacobianRawValues i).2=(gJacobianRepresentatives i).2*(gJacobianCoordinateFactors i).2^2 := by
  fin_cases i <;> norm_num [gJacobianRawValues,gJacobianRepresentatives,gJacobianCoordinateFactors]

private theorem gJacobian_raw_squareclasses(i:Fin 4):
    gJacobianPairClass (gJacobianRawValues i)=gJacobianBasis i := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (gJacobianCoordinateFactors i).1
    · fin_cases i <;> norm_num [gJacobianRawValues]
    · fin_cases i <;> norm_num [gJacobianRepresentatives]
    · fin_cases i <;> norm_num [gJacobianCoordinateFactors]
    · exact (gJacobian_coordinate_factors i).1
  · apply squareClass_eq_of_factor _ _ (gJacobianCoordinateFactors i).2
    · fin_cases i <;> norm_num [gJacobianRawValues]
    · fin_cases i <;> norm_num [gJacobianRepresentatives]
    · fin_cases i <;> norm_num [gJacobianCoordinateFactors]
    · exact (gJacobian_coordinate_factors i).2

theorem gJacobian_descent_coordinates(i:Fin 4):
    completeDescentCoordinates (E 99 49) 0 (-9801) (-2401)
      (gJacobianSplitEquiv (gJacobianFourPoints i))=gJacobianBasis i := by
  rw [←gJacobian_raw_squareclasses i]
  fin_cases i <;> norm_num [gJacobianSplitEquiv,gJacobianToSplit,gJacobianFourPoints,
    gJacobianP1,gJacobianP2,gJacobianFour,gJacobianTwo,WeierstrassCurve.Affine.Point.mk,
    completeDescentCoordinates,gJacobianRawValues,gJacobianPairClass]

def gJacobianPaperRepresentatives : Fin 4 → ℚ×ℚ := ![(15,-35),(165,-35),(22,-2),(74,-74)]
def gJacobianPaperRawValues : Fin 4 → ℚ×ℚ := ![(540,-6860),(1485,-5915),(4950,-2450),(7400,-2401/7400)]
def gJacobianPaperFactors : Fin 4 → ℚ×ℚ := ![(6,14),(3,13),(15,35),(10,49/740)]

theorem gJacobian_paper_coordinate_factors(i:Fin 4):
    (gJacobianPaperRawValues i).1=(gJacobianPaperRepresentatives i).1*(gJacobianPaperFactors i).1^2 ∧
    (gJacobianPaperRawValues i).2=(gJacobianPaperRepresentatives i).2*(gJacobianPaperFactors i).2^2 := by
  fin_cases i <;> norm_num [gJacobianPaperRawValues,gJacobianPaperRepresentatives,gJacobianPaperFactors]

private theorem gJacobian_paper_raw_squareclasses(i:Fin 4):
    gJacobianPairClass (gJacobianPaperRawValues i)=gJacobianPairClass (gJacobianPaperRepresentatives i) := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (gJacobianPaperFactors i).1
    · fin_cases i <;> norm_num [gJacobianPaperRawValues]
    · fin_cases i <;> norm_num [gJacobianPaperRepresentatives]
    · fin_cases i <;> norm_num [gJacobianPaperFactors]
    · exact (gJacobian_paper_coordinate_factors i).1
  · apply squareClass_eq_of_factor _ _ (gJacobianPaperFactors i).2
    · fin_cases i <;> norm_num [gJacobianPaperRawValues]
    · fin_cases i <;> norm_num [gJacobianPaperRepresentatives]
    · fin_cases i <;> norm_num [gJacobianPaperFactors]
    · exact (gJacobian_paper_coordinate_factors i).2

theorem gJacobian_paper_descent_coordinates(i:Fin 4):
    completeDescentCoordinates JG (-5734) 1666 4067 (gJacobianFourPoints i)=
      gJacobianPairClass (gJacobianPaperRepresentatives i) := by
  rw [←gJacobian_paper_raw_squareclasses i]
  fin_cases i <;> norm_num [gJacobianFourPoints,gJacobianP1,gJacobianP2,gJacobianFour,gJacobianTwo,
    WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,gJacobianPaperRawValues,gJacobianPairClass]

end Z2Z4Rank6
