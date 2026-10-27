import Z2Z4Rank6.ThirdTwistSelmer3Pool

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod16_00 : splitCoverResiduePossibleFor 16 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod16_01 : splitCoverResiduePossibleFor 16 r2 r3 (-62521612993073,6305451632738134260592463857,-4925729654938424969)=false := by
  decide +kernel
theorem mod16_02 : splitCoverResiduePossibleFor 16 r2 r3 (6610653218,8215,20117630)=false := by
  decide +kernel
theorem mod16_03 : splitCoverResiduePossibleFor 16 r2 r3 (-3134836358146,19188836374735648997542495,-24484641853630)=true := by
  decide +kernel
theorem mod16_04 : splitCoverResiduePossibleFor 16 r2 r3 (2428935639,78181525135,3685262526184785)=false := by
  decide +kernel
theorem mod16_05 : splitCoverResiduePossibleFor 16 r2 r3 (-231663,2016285695965316455,-173034864961113585)=false := by
  decide +kernel
theorem mod16_06 : splitCoverResiduePossibleFor 16 r2 r3 (328757625729822,25690449159361,732742878)=true := by
  decide +kernel
theorem mod16_07 : splitCoverResiduePossibleFor 16 r2 r3 (-567317166,245439524767537,-139242055615505899640142)=false := by
  decide +kernel
theorem mod16_08 : splitCoverResiduePossibleFor 16 r2 r3 (1,3134836358146,3134836358146)=true := by
  decide +kernel
theorem mod16_09 : splitCoverResiduePossibleFor 16 r2 r3 (-62521612993073,8045653313102818,-186344406846823176027986)=false := by
  decide +kernel
theorem mod16_10 : splitCoverResiduePossibleFor 16 r2 r3 (6610653218,25752680682169390,190266625055)=false := by
  decide +kernel
theorem mod16_11 : splitCoverResiduePossibleFor 16 r2 r3 (-3134836358146,24484641853630,-19188836374735648997542495)=true := by
  decide +kernel
theorem mod16_12 : splitCoverResiduePossibleFor 16 r2 r3 (2428935639,25983790,242306610)=false := by
  decide +kernel
theorem mod16_13 : splitCoverResiduePossibleFor 16 r2 r3 (-231663,24266866506918868496830,-942756497853648690)=false := by
  decide +kernel
theorem mod16_14 : splitCoverResiduePossibleFor 16 r2 r3 (328757625729822,8538273394,998062023)=true := by
  decide +kernel
theorem mod16_15 : splitCoverResiduePossibleFor 16 r2 r3 (-567317166,2953970359941432562,-2288796946343583)=false := by
  decide +kernel
def stage0 : List ECFullTriple := [(1,1,1),(-3134836358146,19188836374735648997542495,-24484641853630),(328757625729822,25690449159361,732742878),(1,3134836358146,3134836358146),(-3134836358146,24484641853630,-19188836374735648997542495),(328757625729822,8538273394,998062023)]
theorem stage0_check : rawPool.filter (splitCoverResiduePossibleFor 16 r2 r3)=stage0 := by
  rw [rawPool_explicit]
  simp only [List.filter_cons,List.filter_nil,mod16_00,mod16_01,mod16_02,mod16_03,mod16_04,mod16_05,mod16_06,mod16_07,mod16_08,mod16_09,mod16_10,mod16_11,mod16_12,mod16_13,mod16_14,mod16_15]
  rfl
theorem stage0_explicit : stage0=[(1,1,1),(-3134836358146,19188836374735648997542495,-24484641853630),(328757625729822,25690449159361,732742878),(1,3134836358146,3134836358146),(-3134836358146,24484641853630,-19188836374735648997542495),(328757625729822,8538273394,998062023)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer3
