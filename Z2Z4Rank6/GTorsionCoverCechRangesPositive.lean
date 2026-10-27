module

public import Z2Z4Rank6.GTorsionCoverOverlap
public import Z2Z4Rank6.GTorsionCoverCechRangesHelpers

@[expose] public section

/-! The signed torsion-cover affine restriction has precisely the
positive Laurent range, with injectivity proved from the free basis.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GTorsionCoverCechRanges
noncomputable section
open GTorsionCoverLaurent GTorsionCoverOverlap

abbrev Poly := Polynomial ℚ

def positiveRestriction (ε : Bool) : GTorsionCoverAffine.CoordinateRing ε →ₗ[ℚ] FourLaurent :=
  (overlapCoordinates ε).toLinearMap.comp (affineRestriction ε)

@[simp] theorem positiveRestriction_apply (ε : Bool)
    (c : GTorsionCoverAffine.CoordinateRing ε) (i : Fin 4) :
    positiveRestriction ε c i = ((affineBasis ε).repr c i).toLaurent :=
  overlapCoordinates_affineRestriction ε c i

theorem positiveRestriction_range (ε : Bool) :
    LinearMap.range (positiveRestriction ε) = positiveFour := by
  rw [←polynomialTupleMap_range]
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨fun i => (affineBasis ε).repr c i,?_⟩
    funext i
    rw [polynomialTupleMap_apply,positiveRestriction_apply]
  · rintro ⟨p,rfl⟩
    let coeffs : Fin 4 →₀ Poly := (Finsupp.linearEquivFunOnFinite Poly Poly (Fin 4)).symm p
    let c : GTorsionCoverAffine.CoordinateRing ε := (affineBasis ε).repr.symm coeffs
    refine ⟨c,?_⟩
    funext i
    rw [polynomialTupleMap_apply,positiveRestriction_apply]
    have hc : (affineBasis ε).repr c i = p i := by
      change (affineBasis ε).repr ((affineBasis ε).repr.symm coeffs) i = p i
      rw [(affineBasis ε).repr.apply_symm_apply]
      rfl
    exact congrArg Polynomial.toLaurent hc

theorem positiveRestriction_injective (ε : Bool) : Function.Injective (positiveRestriction ε) := by
  intro c d h
  apply (affineBasis ε).repr.injective
  apply Finsupp.ext
  intro i
  apply Polynomial.toLaurent_injective
  have hi := congrFun h i
  rw [positiveRestriction_apply,positiveRestriction_apply] at hi
  exact hi

theorem affineRestriction_injective (ε : Bool) : Function.Injective (affineRestriction ε) := by
  intro c d h
  apply positiveRestriction_injective ε
  exact congrArg (overlapCoordinates ε) h

end
end Z2Z4Rank6.GTorsionCoverCechRanges
