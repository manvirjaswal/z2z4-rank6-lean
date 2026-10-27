module

public import Z2Z4Rank6.TorsionCoverRingDimension
public import Z2Z4Rank6.SecondTorsionCoverInfinity

@[expose] public section

/-! Exact dimension 1 of the second torsion-cover chart rings, via
the proved generic integral-polynomial dimension theorem and free 8 basis.
Source: Jaswal, Theorem 8.1(c), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.SecondTorsionCoverDimension
noncomputable section
open AlgebraicGeometry

theorem affine_ringKrullDim (ε:Bool) : ringKrullDim (SecondTorsionCoverAffine.CoordinateRing ε)=1 :=
  TorsionCoverDimension.coordinate_ringKrullDim _
theorem infinity_ringKrullDim (ε:Bool) : ringKrullDim (SecondTorsionCoverInfinity.CoordinateRing ε)=1 :=
  TorsionCoverDimension.coordinate_ringKrullDim _
theorem affine_topologicalKrullDim (ε:Bool) :
    topologicalKrullDim (SecondTorsionCoverAffine.scheme ε)=1 := by
  change topologicalKrullDim (PrimeSpectrum (SecondTorsionCoverAffine.CoordinateRing ε))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,affine_ringKrullDim]
theorem infinity_topologicalKrullDim (ε:Bool) :
    topologicalKrullDim (SecondTorsionCoverInfinity.scheme ε)=1 := by
  change topologicalKrullDim (PrimeSpectrum (SecondTorsionCoverInfinity.CoordinateRing ε))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,infinity_ringKrullDim]
end
end Z2Z4Rank6.SecondTorsionCoverDimension
