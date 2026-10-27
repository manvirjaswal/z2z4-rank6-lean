import Z2Z4Rank6.TripleSquareCoverSmooth
import Z2Z4Rank6.TorsionCoverPolynomialData

/-!
# Affine smoothness of both signed torsion covers

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 6.1, Theorem 1.2(c).
The affine and infinity rings are the four-variable quotients by
the three printed square equations. Each of the two signs has a separable
radicand product, already proved by exact polynomial identities. The generic
maximal-minor calculation therefore proves relative-dimension-one
smoothness over Q.
-/
namespace Z2Z4Rank6.TorsionCoverSmooth
noncomputable section
open scoped BigOperators
open AlgebraicGeometry
open TorsionCoverPolynomialData

/-- The displayed affine quotient is locally standard smooth of dimension 1. -/
theorem affine_locally_standard_smooth (ε:Bool) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (affineRadicand ε))) :=
  TripleSquareCoverSmooth.locally_standard_smooth _ (affine_product_separable ε)

/-- The chart at infinity is locally standard smooth of dimension 1. -/
theorem infinity_locally_standard_smooth (ε:Bool) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (infinityRadicand ε))) :=
  TripleSquareCoverSmooth.locally_standard_smooth _ (infinity_product_separable ε)

/-- Scheme smoothness on the printed affine chart, for both signs. -/
theorem affine_structureMap_smooth (ε:Bool) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (affineRadicand ε))))) :=
  TripleSquareCoverSmooth.structureMap_smooth _ (affine_product_separable ε)

/-- Scheme smoothness on the infinity chart, for both signs. -/
theorem infinity_structureMap_smooth (ε:Bool) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (TripleSquareCover.CoordinateRing (infinityRadicand ε))))) :=
  TripleSquareCoverSmooth.structureMap_smooth _ (infinity_product_separable ε)

end
end Z2Z4Rank6.TorsionCoverSmooth
