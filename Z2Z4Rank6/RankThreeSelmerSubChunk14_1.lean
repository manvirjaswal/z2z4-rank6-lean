module

public import Z2Z4Rank6.RankThreeSelmerData

@[expose] public section

/-! Kernel check of 1024 covering triples. -/
namespace Z2Z4Rank6.RankThreeSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem subChunk_14_1 :
    (rawSubChunk 220457 [143, 311, 517, 611]).filter localTest = subSurvivors 220457 1 := by
  decide +kernel
end Z2Z4Rank6.RankThreeSelmer
