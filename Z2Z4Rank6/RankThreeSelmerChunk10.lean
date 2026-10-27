import Z2Z4Rank6.RankThreeSelmerSubChunk10_0
import Z2Z4Rank6.RankThreeSelmerSubChunk10_1
import Z2Z4Rank6.RankThreeSelmerSubChunk10_2
import Z2Z4Rank6.RankThreeSelmerSubChunk10_3

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_10 : (rawChunk 11603).filter localTest = survivorChunk 11603 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_10_0, subChunk_10_1, subChunk_10_2, subChunk_10_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
