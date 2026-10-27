module

public import Z2Z4Rank6.ReductionCheck
public import Z2Z4Rank6.Twists

@[expose] public section

/-!
# Rational coordinate checks for Proposition 5.1

The rational points and scaling below are the signed formulas printed in
Manvir Jaswal, DOI 10.5281/zenodo.23437117, Proposition 5.1.
They are checked against the six sections.
-/

namespace Z2Z4Rank6.ReductionData

/-- The first coordinate of the printed base point c0. -/
def baseM : ℚ := 7401 / 2399
/-- The positive u-coordinate of the printed base point c0. -/
def baseU : ℚ := 88235 / 2399
/-- The positive v-coordinate of the printed base point c0. -/
def baseV : ℚ := 86835 / 2399
/-- The printed scaling from X at c0 to the coprime integral model E0. -/
def scale : ℚ := 2399^4 / 1234800

/-- The printed rational triple lies on C. -/
theorem base_on_curve : baseU^2 = q1 (baseM^2) ∧ baseV^2 = q2 (baseM^2) := by
  norm_num [baseM, baseU, baseV, q1, q2]

/-- The scaling sends the two curve parameters to printed a0,b0. -/
theorem scale_parameters : scale * a baseM = (a0 : ℚ) ∧
    scale * b baseM = (b0 : ℚ) := by
  norm_num [scale, baseM, a, b, a0, b0]

/-- Each of the six printed abscissae is the scaled abscissa of the
corresponding section, in the same order. -/
theorem rationalX_eq_scaled_section (j : Fin 6) :
    rationalX j = scale^2 * sixX baseM j := by
  fin_cases j <;>
    norm_num [rationalX, scale, baseM, sixX, p1x, p2x, p3x,
      p4x, p5x, p6x, t4x, t5x, t6x, q1, q2, q12]

/-- Each ordinate is the scaled ordinate with the paper's signs and
positive u0,v0; no column sign changes are needed. -/
theorem rationalY_eq_scaled_section (j : Fin 6) :
    rationalY j = scale^3 * sixY baseM baseU baseV j := by
  fin_cases j <;>
    norm_num [rationalY, scale, baseM, baseU, baseV, sixY, p1y, p2y, p3y,
      p4y, p5y, p6y, t4y, t5y, t6y, twistN, q1, q2, q12]

/-- The coprime integral model E0 from Proposition 5.1, over Q. -/
def rationalCurve : WeierstrassCurve ℚ := E (a0 : ℚ) (b0 : ℚ)

instance rationalCurveElliptic : rationalCurve.IsElliptic := by
  constructor
  norm_num [rationalCurve, E, a0, b0, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- The six signed printed points as rational elliptic-curve points. -/
def rationalPoint (j : Fin 6) : rationalCurve.toAffine.Point :=
  .mk (x := rationalX j) (y := rationalY j) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    fin_cases j <;> norm_num [rationalCurve, E, a0, b0, rationalX, rationalY])

end Z2Z4Rank6.ReductionData
