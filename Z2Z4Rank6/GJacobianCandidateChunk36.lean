module

public import Z2Z4Rank6.GJacobianCandidateBase

@[expose] public section
/-! A bounded exact candidate check. -/
namespace Z2Z4Rank6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem gJacobianCandidate_chunk_36 :
    (gJacobianRawChunk (3:ℤ) 0).filter
      (fun d=>intSquareTest (d.1*d.2.1*d.2.2))=gJacobianResultChunk (3:ℤ) 0 := by
  decide +kernel
end Z2Z4Rank6
