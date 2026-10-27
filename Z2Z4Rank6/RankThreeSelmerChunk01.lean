module

public import Z2Z4Rank6.RankThreeSelmerSubChunk01_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk01_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk01_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk01_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_01 : (rawChunk 17).filter localTest = survivorChunk 17 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_01_0, subChunk_01_1, subChunk_01_2, subChunk_01_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
