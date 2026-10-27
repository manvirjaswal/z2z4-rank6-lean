module

public import Z2Z4Rank6.RankThreeSelmerSubChunk04_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk04_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk04_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk04_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_04 : (rawChunk 283).filter localTest = survivorChunk 283 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_04_0, subChunk_04_1, subChunk_04_2, subChunk_04_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
