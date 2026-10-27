import Z2Z4Rank6.RankThreeSelmerSubChunk14_0
import Z2Z4Rank6.RankThreeSelmerSubChunk14_1
import Z2Z4Rank6.RankThreeSelmerSubChunk14_2
import Z2Z4Rank6.RankThreeSelmerSubChunk14_3

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_14 : (rawChunk 220457).filter localTest = survivorChunk 220457 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_14_0, subChunk_14_1, subChunk_14_2, subChunk_14_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
