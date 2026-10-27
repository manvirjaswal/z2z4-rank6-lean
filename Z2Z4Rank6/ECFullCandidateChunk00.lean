import Z2Z4Rank6.ECFullSelmerCandidateBase

/-! A bounded candidate check. -/
namespace Z2Z4Rank6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem ecFullCandidate_chunk_00 :
    (ecFullRawCandidateChunk (-66 : ℤ)).filter
      (fun d => intSquareTest (d.1*d.2.1*d.2.2)) =
        ecFullCandidateSurvivorChunk (-66 : ℤ) := by
  decide +kernel
end Z2Z4Rank6
