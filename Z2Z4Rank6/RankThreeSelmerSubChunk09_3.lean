module

public import Z2Z4Rank6.RankThreeSelmerData

@[expose] public section

/-! Kernel check of 1024 covering triples. -/
namespace Z2Z4Rank6.RankThreeSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem subChunk_09_3 :
    (rawSubChunk 5377 [44473, 160787, 190021, 2090231]).filter localTest = subSurvivors 5377 3 := by
  decide +kernel
end Z2Z4Rank6.RankThreeSelmer
