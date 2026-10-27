module

public import Z2Z4Rank6.TorsionCoverRingDimension
public import Z2Z4Rank6.ThirdTwistCoverInfinity

@[expose] public section

/-! Exact dimension 1 of the third-twist base chart rings, via
the proved generic integral-polynomial dimension theorem and free 8 basis.
Source: Jaswal, third-twist paragraph, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwistCoverDimension
noncomputable section
open AlgebraicGeometry

theorem affine_ringKrullDim  : ringKrullDim (ThirdTwistCoverAffine.CoordinateRing)=1 :=
  TorsionCoverDimension.coordinate_ringKrullDim _
theorem infinity_ringKrullDim  : ringKrullDim (ThirdTwistCoverInfinity.CoordinateRing)=1 :=
  TorsionCoverDimension.coordinate_ringKrullDim _
theorem affine_topologicalKrullDim  :
    topologicalKrullDim (ThirdTwistCoverAffine.scheme)=1 := by
  change topologicalKrullDim (PrimeSpectrum (ThirdTwistCoverAffine.CoordinateRing))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,affine_ringKrullDim]
theorem infinity_topologicalKrullDim  :
    topologicalKrullDim (ThirdTwistCoverInfinity.scheme)=1 := by
  change topologicalKrullDim (PrimeSpectrum (ThirdTwistCoverInfinity.CoordinateRing))=1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,infinity_ringKrullDim]
end
end Z2Z4Rank6.ThirdTwistCoverDimension
