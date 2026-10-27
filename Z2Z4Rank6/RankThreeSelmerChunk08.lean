import Z2Z4Rank6.RankThreeSelmerSubChunk08_0
import Z2Z4Rank6.RankThreeSelmerSubChunk08_1
import Z2Z4Rank6.RankThreeSelmerSubChunk08_2
import Z2Z4Rank6.RankThreeSelmerSubChunk08_3

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_08 : (rawChunk 4811).filter localTest = survivorChunk 4811 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_08_0, subChunk_08_1, subChunk_08_2, subChunk_08_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
