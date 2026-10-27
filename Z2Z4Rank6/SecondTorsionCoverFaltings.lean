import Z2Z4Rank6.SecondTorsionCoverGenus
import Z2Z4Rank6.FaltingsProperCurve
import Z2Z4Rank6.SecondTorsionSquareLiftImage

/-!
# Faltings applied to the genus-nine torsion covers

Jaswal, Section 8, DOI 10.5281/zenodo.23437117. The hypotheses are the published cohomology,
geometric-integrality and proper-curve Faltings statements. This proof uses the projective
covers and does not use hyperelliptic-quotient arithmetic finiteness.
-/
namespace Z2Z4Rank6.SecondTorsionCoverFaltings
noncomputable section
open AlgebraicGeometry CategoryTheory SecondTorsionHyperelliptic
open SecondTorsionCoverProjective SecondTorsionCoverProjectiveRationalPoints
variable (ε : Bool)

theorem finite_rational_points
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Finite (RationalPoint ε) := by
  obtain ⟨hi,hp,_,hd,hc,hfd,hg,_⟩ :=
    SecondTorsionCoverGenus.genus_nine ε hCohom hGeo
  exact FaltingsProperCurve.finite_of_finrank_eq hF (scheme ε) (structureMap ε)
    hp (SecondTorsionCoverProjective.structureMap_smooth_morphism ε)
    hi hd hc hfd 9 hg (by decide)

/-- Every printed affine square lift is a rational point of the
proved proper genus-nine scheme, and conversely. -/
theorem finite_square_lifts
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) : Finite (SquareLift ε) := by
  let : Finite (RationalPoint ε) := finite_rational_points ε hCohom hGeo hF
  exact Finite.of_equiv (RationalPoint ε) (rationalPointEquiv ε).symm

/-- The signed square-obstruction locus is exactly the image of the
square-lift points, including the rational branch points. -/
theorem signed_square_locus_eq_range :
    {c : SecondFamily.G2Point ℚ | IsSquare (sign ε*SecondFamily.V c.W)}=
      Set.range (fun P : SquareLift ε => P.c) := by
  exact signed_square_locus_eq_lift_range ε

theorem finite_signed_square_obstruction
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hF : FaltingsProperCurveTheorem) :
    {c : SecondFamily.G2Point ℚ | IsSquare (sign ε*SecondFamily.V c.W)}.Finite := by
  let : Finite (SquareLift ε) := finite_square_lifts ε hCohom hGeo hF
  exact finite_signed_square_locus_of_finite_lifts ε

end
end Z2Z4Rank6.SecondTorsionCoverFaltings
