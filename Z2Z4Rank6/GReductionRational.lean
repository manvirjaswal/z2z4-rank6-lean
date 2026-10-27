module

public import Z2Z4Rank6.GReductionCheck
public import Z2Z4Rank6.GFunctionFieldSections
public import Z2Z4Rank6.ReductionTheory
public import Z2Z4Rank6.Torsion

@[expose] public section

/-! The exact signed specialization in Proposition 7.2(b), tied to the
five section functions and the printed scaling. -/

namespace Z2Z4Rank6.GReductionData

open GFunctionField

def baseM : ℚ := 291/53
def baseEta : ℚ := 2447004/2809
def scale : ℚ := 7890481/7056

theorem base_on_curve : baseEta^2=h baseM := by norm_num [baseM,baseEta,h]

theorem base_regular : 99-baseM^2 ≠ 0 ∧ baseEta-98*baseM ≠ 0 := by
  norm_num [baseM,baseEta]

theorem scale_parameters : scale*a baseM=(a0:ℚ) ∧ scale*b baseM=(b0:ℚ) := by
  norm_num [scale,baseM,a,b,a0,b0]

theorem rationalX_eq_scaled_section (j : Fin 5) :
    rationalX j=scale^2*fiveX baseM baseEta j := by
  fin_cases j <;> norm_num [rationalX,scale,baseM,baseEta,fiveX,mPrime,delta,p1x,p2x,p3x]

theorem rationalY_eq_scaled_section (j : Fin 5) :
    rationalY j=scale^3*fiveY baseM baseEta j := by
  fin_cases j <;> norm_num [rationalY,scale,baseM,baseEta,fiveY,mPrime,delta,p1y,p2y,p3y]

def rationalCurve : WeierstrassCurve ℚ := E (a0:ℚ) (b0:ℚ)

instance rationalCurveElliptic : rationalCurve.IsElliptic := by
  constructor
  norm_num [rationalCurve,E,a0,b0,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance baseFiberElliptic : (X baseM).IsElliptic := by
  apply E_good (a baseM) (b baseM)
  norm_num [baseM,a,b]

theorem rational_point_equation (j : Fin 5) :
    rationalCurve.toAffine.Equation (rationalX j) (rationalY j) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  fin_cases j <;> norm_num [rationalCurve,E,a0,b0,rationalX,rationalY]

def rationalPoint (j : Fin 5) : rationalCurve.toAffine.Point := .mk (rational_point_equation j)

theorem integral_model (i : Fin 5) : IntegralModelAt (primes i) rationalCurve := by
  unfold IntegralModelAt IntegralAt
  fin_cases i <;> decide +kernel

theorem reduced_model (i : Fin 5) : reducedModel (primes i) rationalCurve=curve i := by
  fin_cases i <;> ext <;> decide +kernel

theorem rational_coordinates_integral (i j : Fin 5) :
    IntegralAt (primes i) (rationalX j) ∧ IntegralAt (primes i) (rationalY j) := by
  unfold IntegralAt
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem rational_coordinates_residue (i j : Fin 5) :
    residue (primes i) (rationalX j)=(reducedX i j : ZMod (primes i)) ∧
      residue (primes i) (rationalY j)=(reducedY i j : ZMod (primes i)) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

end Z2Z4Rank6.GReductionData
