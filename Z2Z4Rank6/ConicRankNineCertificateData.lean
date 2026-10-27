import Z2Z4Rank6.TwoDescent
import Z2Z4Rank6.Torsion

/-! Points and rational square-factor certificates for Dujella–Peral,
Construction of high rank elliptic curves, J. Geom. Anal. 31 (2021), 6698–6724,
Section 7.2, author manuscript p. 19. The integral model is the translated
fiber in Jaswal Proposition 7.1. -/
namespace Z2Z4Rank6.ConicRankNineCertificate
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

def A : ℚ := 46529164800
def B : ℚ := 95880799729
abbrev curve : WeierstrassCurve ℚ := E A B

theorem factor_nonzero : A*B*(A^2-B^2)≠0 := by norm_num [A,B]
instance curveElliptic : curve.IsElliptic := E_good A B factor_nonzero

def xs : Fin 9 → ℚ := ![-3273137615205973785600,39533430105203973120,279478132876851480000,3005279104766882229000,222197754842719031339784,-2627210509891559871840,(412306468294039938235229184/625),(-82026758351823705155000/9),(-219461931428718151505124000/29929)]

def ys : Fin 9 → ℚ := ![146536794948273834785608784102400,28366151318174006313725762657280,80444889264312082025014510440000,435360888401586796986634654929000,107403467027930138123262815935115160,89296070041165035232969369976160,(8443973369284149521648614002510975925248/15625),(-1910373529380200532950203052245000/27),(-1374752529821837436381423204590557548000/5177717)]

def representatives : Fin 11 → ℚ×ℚ := ![(-437431,-5059999),(375259495,421868419855),(3721607,742223),(8179490,172610),(41570696386,3924357394),(-7590,-3990),(571426703601,221508609),(-10032158,-35305838),(-2198556890,-29502129290),(-1,-4180942641098778961),(77452318259486742,68434553555382)]

def squareFactors : Fin 11 → ℚ×ℚ := ![(86502240,14798880),(324576,72288),(8665800,57388200),(19168110,173070270),(2311938,7561206),(588337524,340369596),((26861472/25),(1366552224/25)),((90423350/3),(42088450/3)),((315944460/173),(72405540/173)),(46529164800,(41/46529164800)),(240,9840)]

def parityVectors : Fin 11 → Fin 11 → ZMod 2 :=
  ![![1,0,0,0,0,0,0,0,1,1,0],
    ![0,0,0,1,0,1,0,0,1,0,1],
    ![0,0,0,0,0,0,1,1,0,0,0],
    ![0,1,0,1,1,0,1,1,1,0,0],
    ![0,1,0,0,0,0,1,1,1,0,1],
    ![1,1,1,1,1,0,1,0,0,0,0],
    ![0,0,1,0,0,1,1,1,0,0,1],
    ![1,1,0,0,0,0,0,1,0,1,0],
    ![1,1,0,1,0,0,1,0,0,1,0],
    ![1,0,0,0,0,0,0,0,0,1,1],
    ![0,1,1,0,1,1,1,1,1,1,0]]

theorem point_equation (i : Fin 9) : curve.toAffine.Equation (xs i) (ys i) := by
  change (E A B).toAffine.Equation (xs i) (ys i)
  rw [E_equation_iff]
  fin_cases i <;> norm_num [xs,ys,A,B]

def points (i : Fin 9) : RationalPoints curve := .mk (point_equation i)
def two : RationalPoints curve := twoLeft A B factor_nonzero
def four : RationalPoints curve := fourPoint A B factor_nonzero

def elevenPoints : Fin 11 → RationalPoints curve :=
  ![points 0,points 1,points 2,points 3,points 4,points 5,points 6,points 7,points 8,two,four]

def rawValues : Fin 11 → ℚ×ℚ :=
  ![(xs 0,xs 0+A^2),(xs 1,xs 1+A^2),(xs 2,xs 2+A^2),(xs 3,xs 3+A^2),(xs 4,xs 4+A^2),(xs 5,xs 5+A^2),(xs 6,xs 6+A^2),(xs 7,xs 7+A^2),(xs 8,xs 8+A^2),
    (-A^2,(A^2-B^2)/A^2),(A*B,A*B+A^2)]

theorem square_factors (i : Fin 11) :
    (rawValues i).1=(representatives i).1*(squareFactors i).1^2 ∧
      (rawValues i).2=(representatives i).2*(squareFactors i).2^2 := by
  fin_cases i <;> norm_num [rawValues,representatives,squareFactors,xs,A,B]

noncomputable def squareclasses : Fin 11 → RatSquareClassAdd×RatSquareClassAdd :=
  fun i => (squareClass (representatives i).1,squareClass (representatives i).2)

theorem raw_squareclasses (i : Fin 11) :
    (squareClass (rawValues i).1,squareClass (rawValues i).2)=squareclasses i := by
  apply Prod.ext
  · apply squareClass_eq_of_factor _ _ (squareFactors i).1
    · fin_cases i <;> norm_num [rawValues,xs,A,B]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (square_factors i).1
  · apply squareClass_eq_of_factor _ _ (squareFactors i).2
    · fin_cases i <;> norm_num [rawValues,xs,A,B]
    · fin_cases i <;> norm_num [representatives]
    · fin_cases i <;> norm_num [squareFactors]
    · exact (square_factors i).2

theorem descent_coordinates (i : Fin 11) :
    completeDescentCoordinates curve 0 (-(A^2)) (-(B^2)) (elevenPoints i)=squareclasses i := by
  rw [←raw_squareclasses i]
  fin_cases i <;> norm_num [elevenPoints,points,two,four,twoLeft,fourPoint,
    WeierstrassCurve.Affine.Point.mk,completeDescentCoordinates,rawValues,xs,ys,A,B]

end
end Z2Z4Rank6.ConicRankNineCertificate
