module

public import Z2Z4Rank6.RankThreeSelmerSubChunk11_0
public import Z2Z4Rank6.RankThreeSelmerSubChunk11_1
public import Z2Z4Rank6.RankThreeSelmerSubChunk11_2
public import Z2Z4Rank6.RankThreeSelmerSubChunk11_3

@[expose] public section

/-! Assembly of four kernel checks. -/
namespace Z2Z4Rank6.RankThreeSelmer
theorem chunk_11 : (rawChunk 13243).filter localTest = survivorChunk 13243 := by
  simp only [rawChunk,bBlocks,List.flatMap_cons,List.flatMap_nil,
    List.filter_append,List.filter_nil,subChunk_11_0, subChunk_11_1, subChunk_11_2, subChunk_11_3]
  rfl
end Z2Z4Rank6.RankThreeSelmer
