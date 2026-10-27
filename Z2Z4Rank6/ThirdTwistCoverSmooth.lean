import Z2Z4Rank6.TripleSquareCoverSmooth
import Z2Z4Rank6.ThirdTwistCoverPolynomialData

/-!
# Affine smoothness of both third-twist base

Jaswal, DOI 10.5281/zenodo.23437117, third-twist paragraph.
The affine and infinity rings are the four-variable quotients by
the three printed square equations. Each of the two signs has a separable
radicand product, already proved by exact polynomial identities. The generic
maximal-minor calculation therefore proves relative-dimension-one
smoothness over Q.
-/
namespace Z2Z4Rank6.ThirdTwistCoverSmooth
noncomputable section
open scoped BigOperators
open AlgebraicGeometry
open ThirdTwistCoverPolynomialData

/-- The displayed affine quotient is locally standard smooth of dimension 1. -/
theorem affine_locally_standard_smooth  :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (affineRadicand))) :=
  TripleSquareCoverSmooth.locally_standard_smooth _ (affine_product_separable)

/-- The chart at infinity is locally standard smooth of dimension 1. -/
theorem infinity_locally_standard_smooth  :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (infinityRadicand))) :=
  TripleSquareCoverSmooth.locally_standard_smooth _ (infinity_product_separable)

/-- Scheme smoothness on the printed affine chart, for both signs. -/
theorem affine_structureMap_smooth  :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (affineRadicand))))) :=
  TripleSquareCoverSmooth.structureMap_smooth _ (affine_product_separable)

/-- Scheme smoothness on the infinity chart, for both signs. -/
theorem infinity_structureMap_smooth  :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (infinityRadicand))))) :=
  TripleSquareCoverSmooth.structureMap_smooth _ (infinity_product_separable)

end
end Z2Z4Rank6.ThirdTwistCoverSmooth
