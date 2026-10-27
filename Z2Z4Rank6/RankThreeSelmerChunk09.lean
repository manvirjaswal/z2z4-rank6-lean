import Z2Z4Rank6.RankThreeSelmerSubChunk09_0
import Z2Z4Rank6.RankThreeSelmerSubChunk09_1
import Z2Z4Rank6.RankThreeSelmerSubChunk09_2
import Z2Z4Rank6.RankThreeSelmerSubChunk09_3

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_09 : (rawChunk 5377).filter localTest = survivorChunk 5377 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_09_0, subChunk_09_1, subChunk_09_2, subChunk_09_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
