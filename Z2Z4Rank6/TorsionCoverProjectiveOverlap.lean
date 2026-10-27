module

public import Z2Z4Rank6.TorsionCoverProjectiveOverlapCore
public import Z2Z4Rank6.TorsionCoverInfinityRestriction

@[expose] public section
namespace Z2Z4Rank6.TorsionCoverProjectiveSections
noncomputable section
open scoped Classical
open TorsionCoverProjective TorsionCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mToActualOverlap_eq (ε : Bool) :
    mToActualOverlap ε=(TorsionCoverOverlap.infinityRestriction ε).toRingHom.comp
      (mChartRingEquiv ε).toRingEquiv.toRingHom := by
  apply chartRingHom_ext (S:=ActualOverlap ε) ε 0 rfl (mToActualOverlap ε)
    ((TorsionCoverOverlap.infinityRestriction ε).toRingHom.comp
      (mChartRingEquiv ε).toRingEquiv.toRingHom)
  intro i
  change homogeneousOverlapEquiv ε (mAway ε (mRatio ε i))=
    TorsionCoverOverlap.infinityRestriction ε (chartToInfinity ε (mRatio ε i))
  rw [homogeneousOverlapEquiv_mAway_ratio,chartToInfinity_ratio]
  fin_cases i
  all_goals simp [weights,TorsionCoverOverlap.m_mul_inverseM]

end
end Z2Z4Rank6.TorsionCoverProjectiveSections
