import Z2Z4Rank6.ECFullSelmerData

/-! A bounded stage of the full two-descent certificate for E_C. -/

namespace Z2Z4Rank6

theorem ecFullRealCandidates_check :
    ecFullCandidates.filter (fun d => decide (0<d.2.1)) = ecFullRealCandidates := by
  decide +kernel

theorem ecFullNegativeCandidates_sign :
    ∀ d ∈ ecFullCandidates, ¬0<d.2.1 → d.2.1<0 ∧ d.1*d.2.2<0 := by
  decide +kernel


end Z2Z4Rank6
