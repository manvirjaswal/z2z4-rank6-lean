import Z2Z4Rank6.RankThreeSelmerData

/-! Kernel check of 1024 covering triples. -/
namespace Z2Z4Rank6.RankThreeSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem subChunk_00_3 :
    (rawSubChunk 1 [44473, 160787, 190021, 2090231]).filter localTest = subSurvivors 1 3 := by
  decide +kernel
end Z2Z4Rank6.RankThreeSelmer
