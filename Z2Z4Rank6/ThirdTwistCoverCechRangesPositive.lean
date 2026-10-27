module

public import Z2Z4Rank6.ThirdTwistCoverOverlap
public import Z2Z4Rank6.ThirdTwistCoverCechRangesHelpers

@[expose] public section

/-! The third-twist base affine restriction has precisely the
positive Laurent range, with injectivity proved from the free basis.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwistCoverCechRanges
noncomputable section
open ThirdTwistCoverLaurent ThirdTwistCoverOverlap

abbrev Poly := Polynomial ℚ

def positiveRestriction  : ThirdTwistCoverAffine.CoordinateRing →ₗ[ℚ] EightLaurent :=
  (overlapCoordinates).toLinearMap.comp (affineRestriction)

@[simp] theorem positiveRestriction_apply 
    (c : ThirdTwistCoverAffine.CoordinateRing) (i : Fin 8) :
    positiveRestriction c i = ((affineBasis).repr c i).toLaurent :=
  overlapCoordinates_affineRestriction c i

theorem positiveRestriction_range  :
    LinearMap.range (positiveRestriction) = positiveEight := by
  rw [←polynomialTupleMap_range]
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨fun i => (affineBasis).repr c i,?_⟩
    funext i
    rw [polynomialTupleMap_apply,positiveRestriction_apply]
  · rintro ⟨p,rfl⟩
    let coeffs : Fin 8 →₀ Poly := (Finsupp.linearEquivFunOnFinite Poly Poly (Fin 8)).symm p
    let c : ThirdTwistCoverAffine.CoordinateRing := (affineBasis).repr.symm coeffs
    refine ⟨c,?_⟩
    funext i
    rw [polynomialTupleMap_apply,positiveRestriction_apply]
    have hc : (affineBasis).repr c i = p i := by
      change (affineBasis).repr ((affineBasis).repr.symm coeffs) i = p i
      rw [(affineBasis).repr.apply_symm_apply]
      rfl
    exact congrArg Polynomial.toLaurent hc

theorem positiveRestriction_injective  : Function.Injective (positiveRestriction) := by
  intro c d h
  apply (affineBasis).repr.injective
  apply Finsupp.ext
  intro i
  apply Polynomial.toLaurent_injective
  have hi := congrFun h i
  rw [positiveRestriction_apply,positiveRestriction_apply] at hi
  exact hi

theorem affineRestriction_injective  : Function.Injective (affineRestriction) := by
  intro c d h
  apply positiveRestriction_injective
  exact congrArg (overlapCoordinates) h

end
end Z2Z4Rank6.ThirdTwistCoverCechRanges
