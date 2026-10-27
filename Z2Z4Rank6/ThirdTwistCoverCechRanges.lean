import Z2Z4Rank6.ThirdTwistCoverCechRangesPositive
import Z2Z4Rank6.ThirdTwistCoverInfinityCoordinates

/-! The third-twist base chart restrictions have exactly the
positive and negative Laurent coefficient ranges. Polynomial bases
and localization maps supply every range witness and injectivity.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwistCoverCechRanges
noncomputable section
open ThirdTwistCoverLaurent ThirdTwistCoverOverlap ThirdTwistCoverCechRangesHelpers

def negativeRestriction  : ThirdTwistCoverInfinity.CoordinateRing →ₗ[ℚ] EightLaurent :=
  (overlapCoordinates).toLinearMap.comp (infinityRestriction).toLinearMap

@[simp] theorem negativeRestriction_apply 
    (c : ThirdTwistCoverInfinity.CoordinateRing) (i : Fin 8) :
    negativeRestriction c i =
      AffineBaseFunctionFieldIso.reversePolynomial ((infinityBasis).repr c i) *
        LaurentPolynomial.T (-weights i) :=
  overlapCoordinates_infinityRestriction c i

theorem negativeRestriction_range  :
    LinearMap.range (negativeRestriction) = negativeEight := by
  rw [←negativePolynomialTupleMap_range]
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨fun i => (infinityBasis).repr c i,?_⟩
    funext i
    rw [negativePolynomialTupleMap_apply,negativeRestriction_apply,
      AffineBaseFunctionFieldIso.reversePolynomial_eq_invert]
  · rintro ⟨p,rfl⟩
    let coeffs : Fin 8 →₀ Poly := (Finsupp.linearEquivFunOnFinite Poly Poly (Fin 8)).symm p
    let c : ThirdTwistCoverInfinity.CoordinateRing := (infinityBasis).repr.symm coeffs
    refine ⟨c,?_⟩
    funext i
    have hc : (infinityBasis).repr c i = p i := by
      change (infinityBasis).repr ((infinityBasis).repr.symm coeffs) i = p i
      rw [(infinityBasis).repr.apply_symm_apply]
      rfl
    rw [negativePolynomialTupleMap_apply,negativeRestriction_apply,hc,
      AffineBaseFunctionFieldIso.reversePolynomial_eq_invert]

theorem negativeRestriction_injective  : Function.Injective (negativeRestriction) := by
  intro c d h
  apply (infinityBasis).repr.injective
  apply Finsupp.ext
  intro i
  apply AffineBaseFunctionFieldIso.reversePolynomial_injective
  have hi := congrFun h i
  rw [negativeRestriction_apply,negativeRestriction_apply] at hi
  exact (LaurentPolynomial.isUnit_T (-weights i)).mul_right_cancel hi

theorem infinityRestriction_injective  : Function.Injective (infinityRestriction) := by
  intro c d h
  apply negativeRestriction_injective
  exact congrArg (overlapCoordinates) h

end
end Z2Z4Rank6.ThirdTwistCoverCechRanges
