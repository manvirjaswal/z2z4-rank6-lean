import Z2Z4Rank6.ECFullSelmerData

/-! Exact mod 25 check for one full two-covering. -/
namespace Z2Z4Rank6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem ecFullMod25_chunk_15 :
    splitCoverResiduePossible 25 (66,3,22) = true := by
  decide +kernel
end Z2Z4Rank6
