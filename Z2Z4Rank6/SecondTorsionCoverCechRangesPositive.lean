import Z2Z4Rank6.SecondTorsionCoverOverlap
import Z2Z4Rank6.SecondTorsionCoverCechRangesHelpers

/-! The signed torsion-cover affine restriction has precisely the
positive Laurent range, with injectivity proved from the free basis.
Source: Jaswal, Section 8, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.SecondTorsionCoverCechRanges
noncomputable section
open SecondTorsionCoverLaurent SecondTorsionCoverOverlap

abbrev Poly := Polynomial ℚ

def positiveRestriction (ε : Bool) : SecondTorsionCoverAffine.CoordinateRing ε →ₗ[ℚ] EightLaurent :=
  (overlapCoordinates ε).toLinearMap.comp (affineRestriction ε)

@[simp] theorem positiveRestriction_apply (ε : Bool)
    (c : SecondTorsionCoverAffine.CoordinateRing ε) (i : Fin 8) :
    positiveRestriction ε c i = ((affineBasis ε).repr c i).toLaurent :=
  overlapCoordinates_affineRestriction ε c i

theorem positiveRestriction_range (ε : Bool) :
    LinearMap.range (positiveRestriction ε) = positiveEight := by
  rw [←polynomialTupleMap_range]
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨fun i => (affineBasis ε).repr c i,?_⟩
    funext i
    rw [polynomialTupleMap_apply,positiveRestriction_apply]
  · rintro ⟨p,rfl⟩
    let coeffs : Fin 8 →₀ Poly := (Finsupp.linearEquivFunOnFinite Poly Poly (Fin 8)).symm p
    let c : SecondTorsionCoverAffine.CoordinateRing ε := (affineBasis ε).repr.symm coeffs
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
end Z2Z4Rank6.SecondTorsionCoverCechRanges
