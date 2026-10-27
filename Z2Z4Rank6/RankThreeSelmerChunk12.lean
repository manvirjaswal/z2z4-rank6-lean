import Z2Z4Rank6.RankThreeSelmerSubChunk12_0
import Z2Z4Rank6.RankThreeSelmerSubChunk12_1
import Z2Z4Rank6.RankThreeSelmerSubChunk12_2
import Z2Z4Rank6.RankThreeSelmerSubChunk12_3

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_12 : (rawChunk 91409).filter localTest = survivorChunk 91409 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_12_0, subChunk_12_1, subChunk_12_2, subChunk_12_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
