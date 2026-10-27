module

public import Z2Z4Rank6.RankThreeSelmerSubChunk06_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk06_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk06_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk06_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_06 : (rawChunk 697).filter localTest = survivorChunk 697 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_06_0, subChunk_06_1, subChunk_06_2, subChunk_06_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
