import Z2Z4Rank6.SecondReductionCheck
import Z2Z4Rank6.SecondSections
import Z2Z4Rank6.ReductionTheory

/-!
# The rational specialization in Section 8(d)

The printed G₂ coordinates and all six abscissae are checked against the
signed section functions, with the printed scaling to E_{a,b}.
-/

namespace Z2Z4Rank6.SecondReductionData

open SecondFamily

def baseTheta : ℚ := 857/140
def baseS1 : ℚ := 23306521/20091929
def baseS2 : ℚ := 1120373240/180827361
def baseS3 : ℚ := 11142156700/7293370227
def baseW : ℚ := baseS1^2
def scale : ℚ := 3633170498469369/1046900

theorem base_theta_coordinates : thetaS1 baseTheta=baseS1 ∧
    thetaS2 baseTheta=baseS2 := by
  norm_num [thetaS1,thetaS2,baseTheta,baseS1,baseS2]

theorem base_on_curve : baseS1^2=baseW ∧ baseS2^2=qA baseW ∧ baseS3^2=qB baseW := by
  norm_num [baseS1,baseS2,baseS3,baseW,qA,qB,beta,gamma]

def basePoint : G2Point ℚ where
  W := baseW
  s1 := baseS1
  s2 := baseS2
  s3 := baseS3
  s1_sq := base_on_curve.1
  s2_sq := base_on_curve.2.1
  s3_sq := base_on_curve.2.2

theorem base_regular : baseW ≠ 0 ∧ qA baseW ≠ 0 ∧ qB baseW ≠ 0 := by
  norm_num [baseW,baseS1,qA,qB,beta,gamma]

instance baseFiberElliptic : (F baseW).IsElliptic := by
  apply basePoint.rational_elliptic_iff.mpr
  norm_num [basePoint,baseW,baseS1,lambda]

theorem scale_parameters :
    scale*((baseS1-1)*(baseS1-lambda))=(a0 : ℚ) ∧
      scale*((baseS1+1)*(baseS1+lambda))=(b0 : ℚ) := by
  norm_num [scale,baseS1,lambda,a0,b0]

/-- All six printed abscissae are the scaled section coordinates. -/
theorem rationalX_eq_scaled_section (j : Fin 6) :
    rationalX j=scale^2*basePoint.sixX j := by
  fin_cases j <;>
    norm_num [rationalX,scale,basePoint,G2Point.sixX,G2Point.untwistedX2,
      G2Point.untwistedX3,G2Point.untwistedX4,G2Point.untwistedX5,
      G2Point.untwistedX6,x1,x2,x3,x4,x5,x6,mu,lambda,beta,gamma,
      sigma,iotaScale,qA,qB,qH,baseW,baseS1]

/-- The signed ordinates are derived from the same section functions. -/
theorem rationalY_eq_scaled_section (j : Fin 6) :
    rationalY j=scale^3*basePoint.sixY j := by
  fin_cases j <;>
    norm_num [rationalY,scale,basePoint,G2Point.sixY,G2Point.untwistedY2,
      G2Point.untwistedY3,G2Point.untwistedY4,G2Point.untwistedY5,
      G2Point.untwistedY6,y1,y2,y3,y4,y5,y6,f2,f6,lambda,beta,gamma,
      sigma,iotaScale,qA,qB,qH,baseW,baseS1,baseS2,baseS3]

def rationalCurve : WeierstrassCurve ℚ := E (a0:ℚ) (b0:ℚ)

instance rationalCurveElliptic : rationalCurve.IsElliptic := by
  constructor
  norm_num [rationalCurve,E,a0,b0,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem rational_point_equation (j : Fin 6) :
    rationalCurve.toAffine.Equation (rationalX j) (rationalY j) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    fin_cases j <;> norm_num [rationalCurve,E,a0,b0,rationalX,rationalY]

def rationalPoint (j : Fin 6) : rationalCurve.toAffine.Point :=
  .mk (rational_point_equation j)

theorem integral_model (i : Fin 6) : IntegralModelAt (primes i) rationalCurve := by
  unfold IntegralModelAt IntegralAt
  fin_cases i <;> decide +kernel

theorem reduced_model (i : Fin 6) : reducedModel (primes i) rationalCurve=curve i := by
  fin_cases i <;> ext <;> decide +kernel

theorem rational_coordinates_integral (i j : Fin 6) :
    IntegralAt (primes i) (rationalX j) ∧ IntegralAt (primes i) (rationalY j) := by
  unfold IntegralAt
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem rational_coordinates_residue (i j : Fin 6) :
    residue (primes i) (rationalX j)=(reducedX i j : ZMod (primes i)) ∧
      residue (primes i) (rationalY j)=(reducedY i j : ZMod (primes i)) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

end Z2Z4Rank6.SecondReductionData
