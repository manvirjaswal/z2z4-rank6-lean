import Z2Z4Rank6.GJacobianCandidateBase
/-! A bounded exact candidate check. -/
namespace Z2Z4Rank6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem gJacobianCandidate_chunk_31 :
    (gJacobianRawChunk (-1:ℤ) 3).filter
      (fun d=>intSquareTest (d.1*d.2.1*d.2.2))=gJacobianResultChunk (-1:ℤ) 3 := by
  decide +kernel
end Z2Z4Rank6
