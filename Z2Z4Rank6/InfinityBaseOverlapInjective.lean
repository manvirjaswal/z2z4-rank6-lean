import Z2Z4Rank6.InfinityBaseOverlapCoordinates

/-! The infinity-chart restriction to the overlap is injective,
by the explicit free polynomial bases and Laurent coordinate formulas. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section

theorem infinityRestriction_injective : Function.Injective infinityRestriction := by
  intro c d h
  apply infinityBasis.repr.injective
  apply Finsupp.ext
  intro i
  apply reversePolynomial_injective
  have hi := congrArg (fun z : OverlapRing=>overlapCoordinates z i) h
  rw [overlapCoordinates_infinityRestriction,overlapCoordinates_infinityRestriction] at hi
  exact (LaurentPolynomial.isUnit_T (-LaurentCechQuotient.weights i)).mul_right_cancel hi
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
