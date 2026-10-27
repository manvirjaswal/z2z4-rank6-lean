module

public import Z2Z4Rank6.RankThreeSelmerSubChunk00_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk00_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk00_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk00_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_00 : (rawChunk 1).filter localTest = survivorChunk 1 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_00_0, subChunk_00_1, subChunk_00_2, subChunk_00_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
