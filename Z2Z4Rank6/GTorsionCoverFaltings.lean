import Z2Z4Rank6.GTorsionCoverGenus
import Z2Z4Rank6.FaltingsProperCurve

/-! Direct Faltings for the proper genus-nine signed covers of G. -/
namespace Z2Z4Rank6.GTorsionCoverFaltings
noncomputable section
open AlgebraicGeometry CategoryTheory
open GTorsionCoverProjective GTorsionCoverProjectiveRationalPoints GTorsionCoverPoints
variable (ε : Bool)

theorem finite_rational_points
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Finite (RationalPoint ε) := by
  obtain ⟨hi,hp,_,hd,hc,hfd,hg,_⟩ := GTorsionCoverGenus.genus_nine ε hCohom hGeo
  exact FaltingsProperCurve.finite_of_finrank_eq hF (scheme ε) (structureMap ε)
    hp (GTorsionCoverProjective.structureMap_smooth_morphism ε) hi hd hc hfd 9 hg (by decide)

theorem finite_square_lifts
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Finite (SquareLift ε) := by
  let : Finite (RationalPoint ε) := finite_rational_points ε hCohom hGeo hF
  exact Finite.of_equiv (RationalPoint ε) (rationalPointEquiv ε).symm

theorem signed_square_locus_eq_range :
    {c : GQuarticPoint | IsSquare (TorsionHyperelliptic.sign ε*a c.m*b c.m)}=
      Set.range (fun P : SquareLift ε=>P.c) := by
  ext c
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨⟨c,r,by rw [pow_two]; exact hr.symm⟩,rfl⟩
  · rintro ⟨P,rfl⟩
    exact ⟨P.r,by rw [←pow_two]; exact P.r_sq.symm⟩

theorem finite_signed_square_obstruction
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : GQuarticPoint | IsSquare (TorsionHyperelliptic.sign ε*a c.m*b c.m)}.Finite := by
  let : Finite (SquareLift ε) := finite_square_lifts ε hCohom hGeo hF
  rw [signed_square_locus_eq_range]
  exact Set.finite_range _
end
end Z2Z4Rank6.GTorsionCoverFaltings
