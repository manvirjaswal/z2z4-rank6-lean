import Z2Z4Rank6.TwoDescent
import Z2Z4Rank6.Torsion
import Z2Z4Rank6.SecondReductionData

/-!
# Seven rational points on the printed second example

The unnumbered rank-seven assertion after Theorem 8.1 of Jaswal,
DOI 10.5281/zenodo.23437117. The seven abscissae are
Q₁,Q₃,Q₅ from Theorem 8.1(d), followed by the four printed extra values.
Positive ordinates and exact descent square factors are derived by rational
integer-square-root arithmetic.
-/
namespace Z2Z4Rank6.SecondExampleRankSeven

noncomputable section

def A : ℚ := 460019200
def B : ℚ := 11180308689
abbrev curve : WeierstrassCurve ℚ := E A B

theorem factor_nonzero : A*B*(A^2-B^2)≠0 := by norm_num [A,B]
instance curveElliptic : curve.IsElliptic := E_good A B factor_nonzero

def xs : Fin 7 → ℚ :=
  ![SecondReductionData.rationalX 0,SecondReductionData.rationalX 2,
    SecondReductionData.rationalX 4,-3478949377821720000,-1520527880418835200,
    -3984141305499992809392000/32041,180588656033172910080/169]

def ys : Fin 7 → ℚ := ![20160664931462925833681385250000/27, 11933832350789075906470717518685372416/5880735125, 48902979030030781451001744384, 37165945009211980824222360000, 15676470078557138752422892800, 576334221182017316112190904375568000/5735339, 28851692768148709320069659996160/2197]

def representatives : Fin 9 → ℚ×ℚ := ![(1, 11640327889), (83517906, 139426), (-1069123, -83), (-1023, -1162343), (-46563, -3580420883), (-80046030, -22189127870), (179695, 436531591618255), (-1, -124787684716960258721), (89290914216438, 836683488005542)]

def squareFactors : Fin 9 → ℚ×ℚ := ![(22344670700/3, 207500/3), (63762816/1805, 2716681856/1805), (2065952, 228972768), (58315800, 1676600), (5714480, 19120), (223098920/179, 13388360/179), (31701312/13, 704/13), (460019200, 1/460019200), (240, 80)]

def parityVectors : Fin 9 → Fin 9 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 0, 0, 1, 0, 0, 0],
    ![1, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![1, 0, 1, 0, 1, 1, 1, 0, 1],
    ![1, 1, 1, 1, 0, 1, 1, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 1, 1, 0, 1, 1, 0, 1, 1]]

theorem point_equation (i : Fin 7) : curve.toAffine.Equation (xs i) (ys i) := by
  change (E A B).toAffine.Equation (xs i) (ys i)
  rw [E_equation_iff]
  fin_cases i <;> norm_num [xs,ys,A,B,SecondReductionData.rationalX]

def points (i : Fin 7) : RationalPoints curve := .mk (point_equation i)
def two : RationalPoints curve := twoLeft A B factor_nonzero
def four : RationalPoints curve := fourPoint A B factor_nonzero

def ninePoints : Fin 9 → RationalPoints curve :=
  ![points 0,points 1,points 2,points 3,points 4,points 5,points 6,two,four]

def rawValues : Fin 9 → ℚ×ℚ :=
  ![(xs 0,xs 0+A^2),(xs 1,xs 1+A^2),(xs 2,xs 2+A^2),
    (xs 3,xs 3+A^2),(xs 4,xs 4+A^2),(xs 5,xs 5+A^2),(xs 6,xs 6+A^2),
    (-A^2,(A^2-B^2)/A^2),(A*B,A*B+A^2)]

/-- All eighteen squareclass identities, including the special two-torsion
coordinate and the printed four-torsion coordinate. -/
theorem square_factors (i : Fin 9) :
    (rawValues i).1=(representatives i).1*(squareFactors i).1^2 ∧
      (rawValues i).2=(representatives i).2*(squareFactors i).2^2 := by
  fin_cases i <;> norm_num [rawValues,representatives,squareFactors,xs,A,B,
    SecondReductionData.rationalX]

/-- Exact comparison with the factorized descent data recorded in pd_sec8d.out. -/
theorem representatives_factorizations : representatives=
    ![(1,89*137*457*2089),(2*3*17*31*61*433,2*7*23*433),
      (-11*83*1171,-83),(-3*11*31,-7*13*53*241),
      (-3*11*17*83,-13*53*83*137*457),
      (-2*3*5*17*31*61*83,-2*5*7*13*23*53*83*241),
      (5*83*433,5*7*23*83*137*241*433*457),
      (-1,-7*13*23*53*89*137*241*401*457*2089),
      (2*3*11*17*31*61*83*433*1171,2*83*89*137*433*457*2089)] := by
  ext i <;> fin_cases i <;> norm_num [representatives]

noncomputable def squareclasses : Fin 9 → RatSquareClassAdd×RatSquareClassAdd :=
  fun i => (squareClass (representatives i).1,squareClass (representatives i).2)

theorem raw_squareclasses (i : Fin 9) :
    (squareClass (rawValues i).1,squareClass (rawValues i).2)=squareclasses i := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (squareFactors i).1
    · fin_cases i <;> norm_num [rawValues,xs,A,B,SecondReductionData.rationalX]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (square_factors i).1
  · apply squareClass_eq_of_factor _ _ (squareFactors i).2
    · fin_cases i <;> norm_num [rawValues,xs,A,B,SecondReductionData.rationalX]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (square_factors i).2

/-- Complete-descent coordinates of all nine rational points. -/
theorem descent_coordinates (i : Fin 9) :
    completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (ninePoints i)=squareclasses i := by
  rw [←raw_squareclasses i]
  fin_cases i <;> norm_num [ninePoints,points,two,four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,rawValues,xs,ys,A,B,
    SecondReductionData.rationalX]

end
end Z2Z4Rank6.SecondExampleRankSeven
