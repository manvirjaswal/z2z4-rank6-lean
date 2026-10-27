import Z2Z4Rank6.ThirdTwistSelmer3Mod27

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod25_00 : splitCoverResiduePossibleFor 25 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod25_01 : splitCoverResiduePossibleFor 25 r2 r3 (-3134836358146,19188836374735648997542495,-24484641853630)=true := by
  decide +kernel
theorem mod25_02 : splitCoverResiduePossibleFor 25 r2 r3 (328757625729822,25690449159361,732742878)=false := by
  decide +kernel
theorem mod25_03 : splitCoverResiduePossibleFor 25 r2 r3 (1,3134836358146,3134836358146)=true := by
  decide +kernel
theorem mod25_04 : splitCoverResiduePossibleFor 25 r2 r3 (-3134836358146,24484641853630,-19188836374735648997542495)=true := by
  decide +kernel
theorem mod25_05 : splitCoverResiduePossibleFor 25 r2 r3 (328757625729822,8538273394,998062023)=false := by
  decide +kernel
def stage2 : List ECFullTriple := [(1,1,1),(-3134836358146,19188836374735648997542495,-24484641853630),(1,3134836358146,3134836358146),(-3134836358146,24484641853630,-19188836374735648997542495)]
theorem stage2_check : stage1.filter (splitCoverResiduePossibleFor 25 r2 r3)=stage2 := by
  rw [stage1_explicit]
  simp only [List.filter_cons,List.filter_nil,mod25_00,mod25_01,mod25_02,mod25_03,mod25_04,mod25_05]
  rfl
theorem stage2_explicit : stage2=[(1,1,1),(-3134836358146,19188836374735648997542495,-24484641853630),(1,3134836358146,3134836358146),(-3134836358146,24484641853630,-19188836374735648997542495)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer3
