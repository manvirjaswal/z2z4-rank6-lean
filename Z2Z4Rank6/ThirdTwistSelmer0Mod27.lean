import Z2Z4Rank6.ThirdTwistSelmer0Mod16

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer0
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod27_00 : splitCoverResiduePossibleFor 27 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod27_01 : splitCoverResiduePossibleFor 27 r2 r3 (37083,1109130515059,269184657)=false := by
  decide +kernel
theorem mod27_02 : splitCoverResiduePossibleFor 27 r2 r3 (-789,340585,-3885)=false := by
  decide +kernel
theorem mod27_03 : splitCoverResiduePossibleFor 27 r2 r3 (2896609,27854202841,17086816561)=true := by
  decide +kernel
theorem mod27_04 : splitCoverResiduePossibleFor 27 r2 r3 (107414951547,188023171,27993)=false := by
  decide +kernel
theorem mod27_05 : splitCoverResiduePossibleFor 27 r2 r3 (-2285424501,6929673977065,-48489614565)=false := by
  decide +kernel
theorem mod27_06 : splitCoverResiduePossibleFor 27 r2 r3 (-47,470,-10)=false := by
  decide +kernel
theorem mod27_07 : splitCoverResiduePossibleFor 27 r2 r3 (37083,6402998,1554)=true := by
  decide +kernel
theorem mod27_08 : splitCoverResiduePossibleFor 27 r2 r3 (-789,235985215970,-2691846570)=true := by
  decide +kernel
theorem mod27_09 : splitCoverResiduePossibleFor 27 r2 r3 (-136140623,13091475335270,-170868165610)=false := by
  decide +kernel
theorem mod27_10 : splitCoverResiduePossibleFor 27 r2 r3 (107414951547,130277870768822,19395845826)=true := by
  decide +kernel
theorem mod27_11 : splitCoverResiduePossibleFor 27 r2 r3 (-2285424501,40004930,-279930)=true := by
  decide +kernel
theorem mod27_12 : splitCoverResiduePossibleFor 27 r2 r3 (1,789,789)=true := by
  decide +kernel
theorem mod27_13 : splitCoverResiduePossibleFor 27 r2 r3 (37083,12651678879,23598521597)=false := by
  decide +kernel
theorem mod27_14 : splitCoverResiduePossibleFor 27 r2 r3 (-789,3885,-340585)=false := by
  decide +kernel
theorem mod27_15 : splitCoverResiduePossibleFor 27 r2 r3 (2896609,21976966041549,13481498266629)=true := by
  decide +kernel
theorem mod27_16 : splitCoverResiduePossibleFor 27 r2 r3 (107414951547,2144751,2454053)=false := by
  decide +kernel
theorem mod27_17 : splitCoverResiduePossibleFor 27 r2 r3 (-2285424501,79045710765,-4250922876865)=false := by
  decide +kernel
theorem mod27_18 : splitCoverResiduePossibleFor 27 r2 r3 (-47,370830,-7890)=false := by
  decide +kernel
theorem mod27_19 : splitCoverResiduePossibleFor 27 r2 r3 (37083,73038,136234)=true := by
  decide +kernel
theorem mod27_20 : splitCoverResiduePossibleFor 27 r2 r3 (-789,2691846570,-235985215970)=true := by
  decide +kernel
theorem mod27_21 : splitCoverResiduePossibleFor 27 r2 r3 (-136140623,10329174039528030,-134814982666290)=false := by
  decide +kernel
theorem mod27_22 : splitCoverResiduePossibleFor 27 r2 r3 (107414951547,1486059362382,1700369150746)=true := by
  decide +kernel
theorem mod27_23 : splitCoverResiduePossibleFor 27 r2 r3 (-2285424501,456330,-24540530)=true := by
  decide +kernel
def stage1 : List ECFullTriple := [(1,1,1),(2896609,27854202841,17086816561),(37083,6402998,1554),(-789,235985215970,-2691846570),(107414951547,130277870768822,19395845826),(-2285424501,40004930,-279930),(1,789,789),(2896609,21976966041549,13481498266629),(37083,73038,136234),(-789,2691846570,-235985215970),(107414951547,1486059362382,1700369150746),(-2285424501,456330,-24540530)]
theorem stage1_check : stage0.filter (splitCoverResiduePossibleFor 27 r2 r3)=stage1 := by
  rw [stage0_explicit]
  simp only [List.filter_cons,List.filter_nil,mod27_00,mod27_01,mod27_02,mod27_03,mod27_04,mod27_05,mod27_06,mod27_07,mod27_08,mod27_09,mod27_10,mod27_11,mod27_12,mod27_13,mod27_14,mod27_15,mod27_16,mod27_17,mod27_18,mod27_19,mod27_20,mod27_21,mod27_22,mod27_23]
  rfl
theorem stage1_explicit : stage1=[(1,1,1),(2896609,27854202841,17086816561),(37083,6402998,1554),(-789,235985215970,-2691846570),(107414951547,130277870768822,19395845826),(-2285424501,40004930,-279930),(1,789,789),(2896609,21976966041549,13481498266629),(37083,73038,136234),(-789,2691846570,-235985215970),(107414951547,1486059362382,1700369150746),(-2285424501,456330,-24540530)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer0
