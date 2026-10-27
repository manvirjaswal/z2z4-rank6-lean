module

public import Z2Z4Rank6.GTorsionCoverNormalForm
public import Z2Z4Rank6.GTorsionCoverInfinity
public import Z2Z4Rank6.IntegralPolynomialDimension

@[expose] public section

/-!
# Dimension of the signed torsion-cover affine chart rings

Both quotient rings are free of rank 4 over Q[t]. Their polynomial
coefficient maps are therefore faithful, and integral lying-over/going-up
 gives exact dimension 1.
These are arithmetic foundations for the covers in Jaswal, Section 6,
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.GTorsionCoverDimension
noncomputable section
open AlgebraicGeometry

theorem coordinate_ringKrullDim (f : Fin 2→Polynomial ℚ) :
    ringKrullDim (DoubleSquareCover.CoordinateRing f)=1 := by
  let : Module.Free (Polynomial ℚ) (DoubleSquareCover.CoordinateRing f) :=
    Module.Free.of_basis (DoubleSquareCover.coordinateBasis f)
  exact IntegralPolynomialDimension.dimension_eq_one _
    (FaithfulSMul.algebraMap_injective (Polynomial ℚ) (DoubleSquareCover.CoordinateRing f))

theorem affine_ringKrullDim (ε : Bool) : ringKrullDim (GTorsionCoverAffine.CoordinateRing ε)=1 :=
  coordinate_ringKrullDim _

theorem infinity_ringKrullDim (ε : Bool) : ringKrullDim (GTorsionCoverInfinity.CoordinateRing ε)=1 :=
  coordinate_ringKrullDim _

theorem affine_topologicalKrullDim (ε : Bool) :
    topologicalKrullDim (GTorsionCoverAffine.scheme ε)=1 := by
  change topologicalKrullDim (PrimeSpectrum (GTorsionCoverAffine.CoordinateRing ε))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,affine_ringKrullDim]

theorem infinity_topologicalKrullDim (ε : Bool) :
    topologicalKrullDim (GTorsionCoverInfinity.scheme ε)=1 := by
  change topologicalKrullDim (PrimeSpectrum (GTorsionCoverInfinity.CoordinateRing ε))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,infinity_ringKrullDim]

end
end Z2Z4Rank6.GTorsionCoverDimension
