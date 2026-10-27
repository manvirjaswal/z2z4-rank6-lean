import Z2Z4Rank6.ECFullSelmerData

/-! A bounded stage of the full two-descent certificate for E_C. -/

namespace Z2Z4Rank6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem ecFullStage8_check :
    ecFullRealCandidates.filter (splitCoverResiduePossible 8) = ecFullStage8 := by
  decide +kernel


end Z2Z4Rank6
