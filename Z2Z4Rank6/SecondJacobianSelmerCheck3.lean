module

public import Z2Z4Rank6.SecondJacobianSelmerData

@[expose] public section
namespace Z2Z4Rank6.SecondJacobianSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem block_check_3 : (rawBlock 3).filter pairGood = survivorBlocks 3 := by
  decide +kernel
end Z2Z4Rank6.SecondJacobianSelmer
