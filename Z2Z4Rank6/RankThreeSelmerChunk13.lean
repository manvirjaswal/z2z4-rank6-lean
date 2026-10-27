module

public import Z2Z4Rank6.RankThreeSelmerSubChunk13_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk13_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk13_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk13_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_13 : (rawChunk 197251).filter localTest = survivorChunk 197251 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_13_0, subChunk_13_1, subChunk_13_2, subChunk_13_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
