import Z2Z4Rank6.RankThreeSelmerSubChunk05_0
import Z2Z4Rank6.RankThreeSelmerSubChunk05_1
import Z2Z4Rank6.RankThreeSelmerSubChunk05_2
import Z2Z4Rank6.RankThreeSelmerSubChunk05_3

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_05 : (rawChunk 323).filter localTest = survivorChunk 323 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_05_0, subChunk_05_1, subChunk_05_2, subChunk_05_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
