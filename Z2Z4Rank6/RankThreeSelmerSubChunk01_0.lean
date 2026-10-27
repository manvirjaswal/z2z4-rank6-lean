import Z2Z4Rank6.RankThreeSelmerData

/-! Kernel check of 1024 covering triples. -/
namespace Z2Z4Rank6.RankThreeSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem subChunk_01_0 :
    (rawSubChunk 17 [1, 11, 13, 47]).filter localTest = subSurvivors 17 0 := by
  decide +kernel
end Z2Z4Rank6.RankThreeSelmer
