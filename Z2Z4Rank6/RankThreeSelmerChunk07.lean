module

public import Z2Z4Rank6.RankThreeSelmerSubChunk07_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk07_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk07_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk07_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_07 : (rawChunk 779).filter localTest = survivorChunk 779 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_07_0, subChunk_07_1, subChunk_07_2, subChunk_07_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
