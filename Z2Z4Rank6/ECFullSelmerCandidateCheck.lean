module

public import Z2Z4Rank6.ECFullSelmerCandidateChunks

@[expose] public section

/-! A bounded stage of the full two-descent certificate for E_C. -/

namespace Z2Z4Rank6

theorem ecFullCandidates_check :
    ecFullRawTriples.filter (fun d => intSquareTest (d.1*d.2.1*d.2.2)) = ecFullCandidates := by
  rw [ecFullRawTriples,List.filter_flatMap]
  calc
    ecDescentDivisors.flatMap (fun a => (ecFullRawCandidateChunk a).filter
      (fun d => intSquareTest (d.1*d.2.1*d.2.2))) =
        ecDescentDivisors.flatMap ecFullCandidateSurvivorChunk :=
      List.flatMap_congr ecFullCandidate_chunks
    _ = ecFullCandidates := by decide +kernel


end Z2Z4Rank6
