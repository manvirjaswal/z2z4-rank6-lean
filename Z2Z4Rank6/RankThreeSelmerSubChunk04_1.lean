import Z2Z4Rank6.RankThreeSelmerData

/-! Kernel check of 1024 covering triples. -/
namespace Z2Z4Rank6.RankThreeSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem subChunk_04_1 :
    (rawSubChunk 283 [143, 311, 517, 611]).filter localTest = subSurvivors 283 1 := by
  decide +kernel
end Z2Z4Rank6.RankThreeSelmer
