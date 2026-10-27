import Z2Z4Rank6.SecondJacobianSelmerData
namespace Z2Z4Rank6.SecondJacobianSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem block_check_7 : (rawBlock 7).filter pairGood = survivorBlocks 7 := by
  decide +kernel
end Z2Z4Rank6.SecondJacobianSelmer
