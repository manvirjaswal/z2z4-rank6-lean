module

public import Z2Z4Rank6.RankThreeSelmerSubChunk03_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk03_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk03_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk03_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_03 : (rawChunk 41).filter localTest = survivorChunk 41 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_03_0, subChunk_03_1, subChunk_03_2, subChunk_03_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
