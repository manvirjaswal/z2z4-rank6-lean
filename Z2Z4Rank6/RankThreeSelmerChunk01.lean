import Z2Z4Rank6.RankThreeSelmerSubChunk01_0
import Z2Z4Rank6.RankThreeSelmerSubChunk01_1
import Z2Z4Rank6.RankThreeSelmerSubChunk01_2
import Z2Z4Rank6.RankThreeSelmerSubChunk01_3

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_01 : (rawChunk 17).filter localTest = survivorChunk 17 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_01_0, subChunk_01_1, subChunk_01_2, subChunk_01_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
