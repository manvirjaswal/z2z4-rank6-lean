module

public import Z2Z4Rank6.ThirdTwistCoverProjectiveOverlapCore
public import Z2Z4Rank6.ThirdTwistCoverInfinityRestriction

@[expose] public section
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveSections
noncomputable section
open scoped Classical
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mToActualOverlap_eq  :
    mToActualOverlap=(ThirdTwistCoverOverlap.infinityRestriction).toRingHom.comp
      (mChartRingEquiv).toRingEquiv.toRingHom := by
  apply chartRingHom_ext (S:=ActualOverlap) 0 rfl (mToActualOverlap)
    ((ThirdTwistCoverOverlap.infinityRestriction).toRingHom.comp
      (mChartRingEquiv).toRingEquiv.toRingHom)
  intro i
  change homogeneousOverlapEquiv (mAway (mRatio i))=
    ThirdTwistCoverOverlap.infinityRestriction (chartToInfinity (mRatio i))
  rw [homogeneousOverlapEquiv_mAway_ratio,chartToInfinity_ratio]
  fin_cases i
  all_goals simp [weights,ThirdTwistCoverOverlap.m_mul_inverseM]

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveSections
