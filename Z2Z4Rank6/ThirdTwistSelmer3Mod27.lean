import Z2Z4Rank6.ThirdTwistSelmer3Mod16

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod27_00 : splitCoverResiduePossibleFor 27 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod27_01 : splitCoverResiduePossibleFor 27 r2 r3 (-3134836358146,19188836374735648997542495,-24484641853630)=true := by
  decide +kernel
theorem mod27_02 : splitCoverResiduePossibleFor 27 r2 r3 (328757625729822,25690449159361,732742878)=true := by
  decide +kernel
theorem mod27_03 : splitCoverResiduePossibleFor 27 r2 r3 (1,3134836358146,3134836358146)=true := by
  decide +kernel
theorem mod27_04 : splitCoverResiduePossibleFor 27 r2 r3 (-3134836358146,24484641853630,-19188836374735648997542495)=true := by
  decide +kernel
theorem mod27_05 : splitCoverResiduePossibleFor 27 r2 r3 (328757625729822,8538273394,998062023)=true := by
  decide +kernel
def stage1 : List ECFullTriple := [(1,1,1),(-3134836358146,19188836374735648997542495,-24484641853630),(328757625729822,25690449159361,732742878),(1,3134836358146,3134836358146),(-3134836358146,24484641853630,-19188836374735648997542495),(328757625729822,8538273394,998062023)]
theorem stage1_check : stage0.filter (splitCoverResiduePossibleFor 27 r2 r3)=stage1 := by
  rw [stage0_explicit]
  simp only [List.filter_cons,List.filter_nil,mod27_00,mod27_01,mod27_02,mod27_03,mod27_04,mod27_05]
  rfl
theorem stage1_explicit : stage1=[(1,1,1),(-3134836358146,19188836374735648997542495,-24484641853630),(328757625729822,25690449159361,732742878),(1,3134836358146,3134836358146),(-3134836358146,24484641853630,-19188836374735648997542495),(328757625729822,8538273394,998062023)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer3
