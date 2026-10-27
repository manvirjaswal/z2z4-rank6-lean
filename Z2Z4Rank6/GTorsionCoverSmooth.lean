module

public import Z2Z4Rank6.GTorsionCoverDoubleSmooth
public import Z2Z4Rank6.GTorsionCoverPolynomialData

@[expose] public section

/-!
# Affine smoothness of both signed torsion covers

Jaswal, DOI 10.5281/zenodo.23437117, Theorem 8.1(c).
The affine and infinity rings are the three-variable quotients by
the two printed square equations. Each of the two signs has a separable
radicand product, already proved by exact polynomial identities. The generic
maximal-minor calculation therefore proves relative-dimension-one
smoothness over Q.
-/
namespace Z2Z4Rank6.GTorsionCoverSmooth
noncomputable section
open scoped BigOperators
open AlgebraicGeometry
open GTorsionCoverPolynomialData

/-- The displayed affine quotient is locally standard smooth of dimension 1. -/
theorem affine_locally_standard_smooth (ε:Bool) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (DoubleSquareCover.CoordinateRing (affineRadicand ε))) :=
  DoubleSquareCoverSmooth.locally_standard_smooth _ (affine_product_separable ε)

/-- The chart at infinity is locally standard smooth of dimension 1. -/
theorem infinity_locally_standard_smooth (ε:Bool) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (DoubleSquareCover.CoordinateRing (infinityRadicand ε))) :=
  DoubleSquareCoverSmooth.locally_standard_smooth _ (infinity_product_separable ε)

/-- Scheme smoothness on the printed affine chart, for both signs. -/
theorem affine_structureMap_smooth (ε:Bool) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (DoubleSquareCover.CoordinateRing (affineRadicand ε))))) :=
  DoubleSquareCoverSmooth.structureMap_smooth _ (affine_product_separable ε)

/-- Scheme smoothness on the infinity chart, for both signs. -/
theorem infinity_structureMap_smooth (ε:Bool) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (DoubleSquareCover.CoordinateRing (infinityRadicand ε))))) :=
  DoubleSquareCoverSmooth.structureMap_smooth _ (infinity_product_separable ε)

end
end Z2Z4Rank6.GTorsionCoverSmooth
