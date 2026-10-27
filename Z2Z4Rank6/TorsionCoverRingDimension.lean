import Z2Z4Rank6.TripleSquareNormalForm
import Z2Z4Rank6.TorsionCoverInfinity
import Z2Z4Rank6.IntegralPolynomialDimension

/-!
# Dimension of the signed torsion-cover affine chart rings

Both quotient rings are free of rank 8 over Q[t]. Their polynomial
coefficient maps are therefore faithful, and integral lying-over/going-up
 gives exact dimension 1.
These are arithmetic foundations for the covers in Jaswal, Section 6,
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.TorsionCoverDimension
noncomputable section
open AlgebraicGeometry

theorem coordinate_ringKrullDim (f : Fin 3→Polynomial ℚ) :
    ringKrullDim (TripleSquareCover.CoordinateRing f)=1 := by
  let : Module.Free (Polynomial ℚ) (TripleSquareCover.CoordinateRing f) :=
    Module.Free.of_basis (TripleSquareCover.coordinateBasis f)
  exact IntegralPolynomialDimension.dimension_eq_one _
    (FaithfulSMul.algebraMap_injective (Polynomial ℚ) (TripleSquareCover.CoordinateRing f))

theorem affine_ringKrullDim (ε : Bool) : ringKrullDim (TorsionCoverAffine.CoordinateRing ε)=1 :=
  coordinate_ringKrullDim _

theorem infinity_ringKrullDim (ε : Bool) : ringKrullDim (TorsionCoverInfinity.CoordinateRing ε)=1 :=
  coordinate_ringKrullDim _

theorem affine_topologicalKrullDim (ε : Bool) :
    topologicalKrullDim (TorsionCoverAffine.scheme ε)=1 := by
  change topologicalKrullDim (PrimeSpectrum (TorsionCoverAffine.CoordinateRing ε))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,affine_ringKrullDim]

theorem infinity_topologicalKrullDim (ε : Bool) :
    topologicalKrullDim (TorsionCoverInfinity.scheme ε)=1 := by
  change topologicalKrullDim (PrimeSpectrum (TorsionCoverInfinity.CoordinateRing ε))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,infinity_ringKrullDim]

end
end Z2Z4Rank6.TorsionCoverDimension
