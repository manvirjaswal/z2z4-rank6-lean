module

public import Z2Z4Rank6.RankThreeSelmerData

@[expose] public section

/-! Kernel check of 1024 covering triples. -/
namespace Z2Z4Rank6.RankThreeSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem subChunk_05_1 :
    (rawSubChunk 323 [143, 311, 517, 611]).filter localTest = subSurvivors 323 1 := by
  decide +kernel
end Z2Z4Rank6.RankThreeSelmer
