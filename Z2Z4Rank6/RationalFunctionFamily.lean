module

public import Z2Z4Rank6.FunctionField
public import Z2Z4Rank6.FamilyIdentities
public import Z2Z4Rank6.PointMap

@[expose] public section

/-!
# The original family over Q(m)

The original rational-function family and three specified points of Lemma 2.2
of M. Jaswal, DOI 10.5281/zenodo.23437117. Ellipticity is checked by
the injective embedding into the function field of C.
-/

namespace Z2Z4Rank6.RationalFunctionFamily

noncomputable section

abbrev Base := FunctionField.Base

def parameter : Base := RatFunc.X

abbrev curve : WeierstrassCurve Base := X parameter

theorem curve_map_to_function_field :
    curve.map (algebraMap Base FunctionField.K) = X FunctionField.m := by
  ext <;> simp [curve, parameter, X, E, a, b, FunctionField.m,
    WeierstrassCurve.map, map_ofNat]

instance curveElliptic : curve.IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  intro h
  have he : (curve.map (algebraMap Base FunctionField.K)).Δ = 0 := by
    rw [WeierstrassCurve.map_Δ, h, map_zero]
  rw [curve_map_to_function_field] at he
  exact (WeierstrassCurve.isUnit_Δ (X FunctionField.m)).ne_zero he

/-- The three printed points on X(Q(m)). -/
def points : Fin 3 → curve.toAffine.Point :=
  ![point1 parameter, point2 parameter, point3 parameter]

theorem parameter_transcendental : Transcendental ℚ parameter := by
  change Transcendental ℚ (RatFunc.X : RatFunc ℚ)
  convert RatFunc.transcendental_X (K := ℚ) using 1
  exact Subsingleton.elim _ _

theorem parameter_ne_one : parameter ≠ 1 := by
  intro h
  exact parameter_transcendental (h ▸ isAlgebraic_one)

theorem parameter_ne_neg_one : parameter ≠ -1 := by
  intro h
  exact parameter_transcendental (h ▸ (isAlgebraic_one.neg))

/-- The printed admissible change of variables over the Q(t). -/
theorem dp_parameter_isomorphism_over_ratfunc :
    scalingChange (Units.mk0 (parameterRho parameter)
      (parameterRho_ne_zero parameter parameter_ne_one parameter_ne_neg_one)) •
      E (dpPlus (parameterAlpha parameter) (1/7))
        (dpMinus (parameterAlpha parameter) (1/7)) =
      X (parameterM parameter) :=
  dp_parameter_isomorphism parameter parameter_ne_one parameter_ne_neg_one

end
end Z2Z4Rank6.RationalFunctionFamily
