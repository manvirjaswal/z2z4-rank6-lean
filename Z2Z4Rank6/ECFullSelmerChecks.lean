module

public import Z2Z4Rank6.ECFullSelmerCandidateCheck
public import Z2Z4Rank6.ECFullSelmerRealCheck
public import Z2Z4Rank6.ECFullSelmerMod8
public import Z2Z4Rank6.ECFullSelmerMod9
public import Z2Z4Rank6.ECFullSelmerMod25

@[expose] public section

namespace Z2Z4Rank6

theorem ecFullSurvivors_card : ecFullSurvivors.toFinset.card = 8 := by decide +kernel


end Z2Z4Rank6
