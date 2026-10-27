module

public import Z2Z4Rank6.RankThreeSelmerSubChunk15_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk15_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk15_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk15_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_15 : (rawChunk 3747769).filter localTest = survivorChunk 3747769 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_15_0, subChunk_15_1, subChunk_15_2, subChunk_15_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
