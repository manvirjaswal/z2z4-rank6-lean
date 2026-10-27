module

public import Z2Z4Rank6.GTorsionCoverCechRangesPositive
public import Z2Z4Rank6.GTorsionCoverInfinityCoordinates

@[expose] public section

/-! The signed torsion-cover chart restrictions have exactly the
positive and negative Laurent coefficient ranges. Polynomial bases
and localization maps supply every range witness and injectivity.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GTorsionCoverCechRanges
noncomputable section
open GTorsionCoverLaurent GTorsionCoverOverlap GTorsionCoverCechRangesHelpers

def negativeRestriction (ε : Bool) : GTorsionCoverInfinity.CoordinateRing ε →ₗ[ℚ] FourLaurent :=
  (overlapCoordinates ε).toLinearMap.comp (infinityRestriction ε).toLinearMap

@[simp] theorem negativeRestriction_apply (ε : Bool)
    (c : GTorsionCoverInfinity.CoordinateRing ε) (i : Fin 4) :
    negativeRestriction ε c i =
      AffineBaseFunctionFieldIso.reversePolynomial ((infinityBasis ε).repr c i) *
        LaurentPolynomial.T (-weights i) :=
  overlapCoordinates_infinityRestriction ε c i

theorem negativeRestriction_range (ε : Bool) :
    LinearMap.range (negativeRestriction ε) = negativeFour := by
  rw [←negativePolynomialTupleMap_range]
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨fun i => (infinityBasis ε).repr c i,?_⟩
    funext i
    rw [negativePolynomialTupleMap_apply,negativeRestriction_apply,
      AffineBaseFunctionFieldIso.reversePolynomial_eq_invert]
  · rintro ⟨p,rfl⟩
    let coeffs : Fin 4 →₀ Poly := (Finsupp.linearEquivFunOnFinite Poly Poly (Fin 4)).symm p
    let c : GTorsionCoverInfinity.CoordinateRing ε := (infinityBasis ε).repr.symm coeffs
    refine ⟨c,?_⟩
    funext i
    have hc : (infinityBasis ε).repr c i = p i := by
      change (infinityBasis ε).repr ((infinityBasis ε).repr.symm coeffs) i = p i
      rw [(infinityBasis ε).repr.apply_symm_apply]
      rfl
    rw [negativePolynomialTupleMap_apply,negativeRestriction_apply,hc,
      AffineBaseFunctionFieldIso.reversePolynomial_eq_invert]

theorem negativeRestriction_injective (ε : Bool) : Function.Injective (negativeRestriction ε) := by
  intro c d h
  apply (infinityBasis ε).repr.injective
  apply Finsupp.ext
  intro i
  apply AffineBaseFunctionFieldIso.reversePolynomial_injective
  have hi := congrFun h i
  rw [negativeRestriction_apply,negativeRestriction_apply] at hi
  exact (LaurentPolynomial.isUnit_T (-weights i)).mul_right_cancel hi

theorem infinityRestriction_injective (ε : Bool) : Function.Injective (infinityRestriction ε) := by
  intro c d h
  apply negativeRestriction_injective ε
  exact congrArg (overlapCoordinates ε) h

end
end Z2Z4Rank6.GTorsionCoverCechRanges
