module

public import Z2Z4Rank6.RankThreeSelmerSubChunk02_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk02_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk02_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk02_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_02 : (rawChunk 19).filter localTest = survivorChunk 19 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_02_0, subChunk_02_1, subChunk_02_2, subChunk_02_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
