module

public import Z2Z4Rank6.RankThreeSelmerData

@[expose] public section

/-! Kernel check of 1024 covering triples. -/
namespace Z2Z4Rank6.RankThreeSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem subChunk_01_2 :
    (rawSubChunk 17 [3421, 4043, 6721, 14617]).filter localTest = subSurvivors 17 2 := by
  decide +kernel
end Z2Z4Rank6.RankThreeSelmer
