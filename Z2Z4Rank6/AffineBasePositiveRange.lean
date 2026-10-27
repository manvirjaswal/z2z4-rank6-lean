import Z2Z4Rank6.PositiveLaurentRange
import Z2Z4Rank6.AffineBaseLaurentBasis

/-!
# The affine chart restriction has the positive Laurent range

Jaswal Section 3, DOI 10.5281/zenodo.23437117. The source is the
affine coordinate quotient, and the map is its m-localization map.
The localized basis 1,u,v,uv gives the Laurent coordinates.
-/

namespace Z2Z4Rank6.AffineBaseCechRanges
noncomputable section
open AffineBaseFunctionFieldIso LaurentCechQuotient PositiveLaurentRange

def positiveRestriction : CoordinateRing→ₗ[ℚ]FourLaurent :=
  overlapCoordinates.toLinearMap.comp affineRestriction

@[simp] theorem positiveRestriction_apply (c : CoordinateRing) (i : Fin 4) :
    positiveRestriction c i=Polynomial.toLaurent (coordinateBasis.repr c i) :=
  overlapCoordinates_algebraMap c i

/-- The image of the coordinate-ring restriction, expressed in the
localized basis, is exactly the positive coefficient submodule. -/
theorem positiveRestriction_range : LinearMap.range positiveRestriction=positiveFour := by
  rw [←polynomialTupleMap_range]
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨fun i => coordinateBasis.repr c i,?_⟩
    apply funext
    intro i
    rw [polynomialTupleMap_apply,positiveRestriction_apply]
  · rintro ⟨p,rfl⟩
    let coeffs : Fin 4→₀Poly := (Finsupp.linearEquivFunOnFinite Poly Poly (Fin 4)).symm p
    let c : CoordinateRing := coordinateBasis.repr.symm coeffs
    refine ⟨c,?_⟩
    apply funext
    intro i
    rw [polynomialTupleMap_apply,positiveRestriction_apply]
    have hc : coordinateBasis.repr c i=p i := by
      change coordinateBasis.repr (coordinateBasis.repr.symm coeffs) i=p i
      rw [coordinateBasis.repr.apply_symm_apply]
      rfl
    exact congrArg Polynomial.toLaurent hc

end
end Z2Z4Rank6.AffineBaseCechRanges
