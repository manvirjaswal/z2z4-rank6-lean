import Z2Z4Rank6.ECFullSelmerCandidateCheck
import Z2Z4Rank6.ECFullSelmerRealCheck
import Z2Z4Rank6.ECFullSelmerMod8
import Z2Z4Rank6.ECFullSelmerMod9
import Z2Z4Rank6.ECFullSelmerMod25

namespace Z2Z4Rank6

theorem ecFullSurvivors_card : ecFullSurvivors.toFinset.card = 8 := by decide +kernel


end Z2Z4Rank6
