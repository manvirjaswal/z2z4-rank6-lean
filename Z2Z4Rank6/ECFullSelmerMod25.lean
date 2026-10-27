import Z2Z4Rank6.ECFullMod25Chunk00
import Z2Z4Rank6.ECFullMod25Chunk01
import Z2Z4Rank6.ECFullMod25Chunk02
import Z2Z4Rank6.ECFullMod25Chunk03
import Z2Z4Rank6.ECFullMod25Chunk04
import Z2Z4Rank6.ECFullMod25Chunk05
import Z2Z4Rank6.ECFullMod25Chunk06
import Z2Z4Rank6.ECFullMod25Chunk07
import Z2Z4Rank6.ECFullMod25Chunk08
import Z2Z4Rank6.ECFullMod25Chunk09
import Z2Z4Rank6.ECFullMod25Chunk10
import Z2Z4Rank6.ECFullMod25Chunk11
import Z2Z4Rank6.ECFullMod25Chunk12
import Z2Z4Rank6.ECFullMod25Chunk13
import Z2Z4Rank6.ECFullMod25Chunk14
import Z2Z4Rank6.ECFullMod25Chunk15

/-! Assembly of independent bounded local checks. -/
namespace Z2Z4Rank6
theorem ecFullStage25_check :
    ecFullStage9.filter (splitCoverResiduePossible 25) = ecFullSurvivors := by
  simp only [ecFullStage9, List.filter_cons, List.filter_nil, ecFullMod25_chunk_00, ecFullMod25_chunk_01, ecFullMod25_chunk_02, ecFullMod25_chunk_03, ecFullMod25_chunk_04, ecFullMod25_chunk_05, ecFullMod25_chunk_06, ecFullMod25_chunk_07, ecFullMod25_chunk_08, ecFullMod25_chunk_09, ecFullMod25_chunk_10, ecFullMod25_chunk_11, ecFullMod25_chunk_12, ecFullMod25_chunk_13, ecFullMod25_chunk_14, ecFullMod25_chunk_15]
  rfl
end Z2Z4Rank6
