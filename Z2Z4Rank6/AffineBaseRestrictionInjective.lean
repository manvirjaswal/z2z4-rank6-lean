import Z2Z4Rank6.AffineBasePositiveRange
import Z2Z4Rank6.NegativeLaurentRange
import Z2Z4Rank6.InfinityBaseOverlapInjective

/-! Both chart restrictions are injective. This lets compatible
pairs be identified with the intersection of their proved Laurent ranges. -/
namespace Z2Z4Rank6
noncomputable section
namespace AffineBaseCechRanges
open AffineBaseFunctionFieldIso

theorem positiveRestriction_injective : Function.Injective positiveRestriction := by
  intro c d h
  apply coordinateBasis.repr.injective
  apply Finsupp.ext
  intro i
  apply Polynomial.toLaurent_injective
  have hi := congrFun h i
  rw [positiveRestriction_apply,positiveRestriction_apply] at hi
  exact hi
end AffineBaseCechRanges
namespace NegativeLaurentRange
open AffineBaseFunctionFieldIso

theorem negativeRestriction_injective : Function.Injective negativeRestriction :=
  overlapCoordinates.injective.comp infinityRestriction_injective
end NegativeLaurentRange
namespace AffineBaseFunctionFieldIso

theorem affineRestriction_injective : Function.Injective affineRestriction := by
  intro c d h
  apply AffineBaseCechRanges.positiveRestriction_injective
  exact congrArg overlapCoordinates h
end AffineBaseFunctionFieldIso
end
end Z2Z4Rank6
