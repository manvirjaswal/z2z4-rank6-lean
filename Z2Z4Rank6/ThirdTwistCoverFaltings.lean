import Z2Z4Rank6.ThirdTwistCoverGenus
import Z2Z4Rank6.FaltingsProperCurve

/-! The third-twist genus-five base has finitely many rational points. -/
namespace Z2Z4Rank6.ThirdTwistCoverFaltings
noncomputable section
open AlgebraicGeometry CategoryTheory ThirdTwistCoverProjective ThirdTwistCoverProjectiveRationalPoints

theorem finite_rational_points
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Finite RationalPoint := by
  obtain ⟨hi,hp,_,hd,hc,hfd,hg,_⟩ := ThirdTwistCoverGenus.genus_five hCohom hGeo
  exact FaltingsProperCurve.finite_of_finrank_eq hF scheme structureMap hp
    ThirdTwistCoverProjective.structureMap_smooth_morphism hi hd hc hfd 5 hg (by decide)

theorem finite_affine_points
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Finite ThirdTwistCoverPoints.Point := by
  let : Finite RationalPoint := finite_rational_points hCohom hGeo hF
  exact Finite.of_equiv RationalPoint rationalPointEquiv.symm
end
end Z2Z4Rank6.ThirdTwistCoverFaltings
