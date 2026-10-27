module

public import Z2Z4Rank6.ThirdTwistSelmer0Mod27

@[expose] public section

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer0
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod25_00 : splitCoverResiduePossibleFor 25 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod25_01 : splitCoverResiduePossibleFor 25 r2 r3 (2896609,27854202841,17086816561)=true := by
  decide +kernel
theorem mod25_02 : splitCoverResiduePossibleFor 25 r2 r3 (37083,6402998,1554)=false := by
  decide +kernel
theorem mod25_03 : splitCoverResiduePossibleFor 25 r2 r3 (-789,235985215970,-2691846570)=true := by
  decide +kernel
theorem mod25_04 : splitCoverResiduePossibleFor 25 r2 r3 (107414951547,130277870768822,19395845826)=false := by
  decide +kernel
theorem mod25_05 : splitCoverResiduePossibleFor 25 r2 r3 (-2285424501,40004930,-279930)=true := by
  decide +kernel
theorem mod25_06 : splitCoverResiduePossibleFor 25 r2 r3 (1,789,789)=true := by
  decide +kernel
theorem mod25_07 : splitCoverResiduePossibleFor 25 r2 r3 (2896609,21976966041549,13481498266629)=true := by
  decide +kernel
theorem mod25_08 : splitCoverResiduePossibleFor 25 r2 r3 (37083,73038,136234)=false := by
  decide +kernel
theorem mod25_09 : splitCoverResiduePossibleFor 25 r2 r3 (-789,2691846570,-235985215970)=true := by
  decide +kernel
theorem mod25_10 : splitCoverResiduePossibleFor 25 r2 r3 (107414951547,1486059362382,1700369150746)=false := by
  decide +kernel
theorem mod25_11 : splitCoverResiduePossibleFor 25 r2 r3 (-2285424501,456330,-24540530)=true := by
  decide +kernel
def stage2 : List ECFullTriple := [(1,1,1),(2896609,27854202841,17086816561),(-789,235985215970,-2691846570),(-2285424501,40004930,-279930),(1,789,789),(2896609,21976966041549,13481498266629),(-789,2691846570,-235985215970),(-2285424501,456330,-24540530)]
theorem stage2_check : stage1.filter (splitCoverResiduePossibleFor 25 r2 r3)=stage2 := by
  rw [stage1_explicit]
  simp only [List.filter_cons,List.filter_nil,mod25_00,mod25_01,mod25_02,mod25_03,mod25_04,mod25_05,mod25_06,mod25_07,mod25_08,mod25_09,mod25_10,mod25_11]
  rfl
theorem stage2_explicit : stage2=[(1,1,1),(2896609,27854202841,17086816561),(-789,235985215970,-2691846570),(-2285424501,40004930,-279930),(1,789,789),(2896609,21976966041549,13481498266629),(-789,2691846570,-235985215970),(-2285424501,456330,-24540530)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer0
