import Z2Z4Rank6.AffineBaseRestrictionInjective
import Z2Z4Rank6.LaurentCechConstants
import Z2Z4Rank6.TwoChartEqualizer

/-!
# Constants among compatible affine chart pairs

The maps here are the coordinate quotient restrictions into the
localized overlap, expressed in its proved Laurent basis. Their
compatible pairs form a rational line. The identification with global
scheme sections is a separate sheaf-gluing step.
-/

namespace Z2Z4Rank6.AffineBaseCechConstants
noncomputable section
open AffineBaseCechRanges NegativeLaurentRange LaurentCechQuotient

def restrictionDifference :=
  TwoChartEqualizer.difference positiveRestriction negativeRestriction

theorem restriction_ranges :
    LinearMap.range positiveRestriction⊓LinearMap.range negativeRestriction=
      positiveFour⊓negativeFour := by
  rw [positiveRestriction_range,negativeRestriction_range]

/-- All compatible pairs of coordinate-ring sections are rational
constants, with compatibility checked in the localized overlap. -/
def compatiblePairsEquiv : LinearMap.ker restrictionDifference≃ₗ[ℚ]ℚ :=
  ((TwoChartEqualizer.compatibleEquivIntersection positiveRestriction negativeRestriction
      positiveRestriction_injective negativeRestriction_injective).trans
    (LinearEquiv.ofEq _ _ restriction_ranges)).trans
      LaurentCechConstants.intersectionFourEquiv

theorem finrank_compatible_pairs : Module.finrank ℚ (LinearMap.ker restrictionDifference)=1 := by
  simpa using compatiblePairsEquiv.finrank_eq

end
end Z2Z4Rank6.AffineBaseCechConstants
