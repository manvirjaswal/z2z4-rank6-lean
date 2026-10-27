import Z2Z4Rank6.SecondFamily

/-! The singular second-family rational parameters form the proved finite range. -/
namespace Z2Z4Rank6.SecondCofiniteSpecialization
open SecondFamily

theorem singularPoints_finite :
    {P : G2Point ℚ | ¬GoodCurve (F P.W)}.Finite := by
  apply (Set.finite_range singularPoint).subset
  intro P hP
  apply (mem_singularPoint_range_iff P).mpr
  have h := P.rational_elliptic_iff
  change ¬(F P.W).IsElliptic at hP
  tauto

end Z2Z4Rank6.SecondCofiniteSpecialization
