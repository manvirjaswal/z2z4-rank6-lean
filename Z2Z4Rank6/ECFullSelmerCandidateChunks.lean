import Z2Z4Rank6.ECFullCandidateChunk00
import Z2Z4Rank6.ECFullCandidateChunk01
import Z2Z4Rank6.ECFullCandidateChunk02
import Z2Z4Rank6.ECFullCandidateChunk03
import Z2Z4Rank6.ECFullCandidateChunk04
import Z2Z4Rank6.ECFullCandidateChunk05
import Z2Z4Rank6.ECFullCandidateChunk06
import Z2Z4Rank6.ECFullCandidateChunk07
import Z2Z4Rank6.ECFullCandidateChunk08
import Z2Z4Rank6.ECFullCandidateChunk09
import Z2Z4Rank6.ECFullCandidateChunk10
import Z2Z4Rank6.ECFullCandidateChunk11
import Z2Z4Rank6.ECFullCandidateChunk12
import Z2Z4Rank6.ECFullCandidateChunk13
import Z2Z4Rank6.ECFullCandidateChunk14
import Z2Z4Rank6.ECFullCandidateChunk15

/-! Assembly of bounded checks. -/
namespace Z2Z4Rank6
theorem ecFullCandidate_chunks (a : ℤ) (ha : a ∈ ecDescentDivisors) :
    (ecFullRawCandidateChunk a).filter (fun d => intSquareTest (d.1*d.2.1*d.2.2)) =
      ecFullCandidateSurvivorChunk a := by
  simp only [ecDescentDivisors,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ecFullCandidate_chunk_00
  · exact ecFullCandidate_chunk_01
  · exact ecFullCandidate_chunk_02
  · exact ecFullCandidate_chunk_03
  · exact ecFullCandidate_chunk_04
  · exact ecFullCandidate_chunk_05
  · exact ecFullCandidate_chunk_06
  · exact ecFullCandidate_chunk_07
  · exact ecFullCandidate_chunk_08
  · exact ecFullCandidate_chunk_09
  · exact ecFullCandidate_chunk_10
  · exact ecFullCandidate_chunk_11
  · exact ecFullCandidate_chunk_12
  · exact ecFullCandidate_chunk_13
  · exact ecFullCandidate_chunk_14
  · exact ecFullCandidate_chunk_15
end Z2Z4Rank6
