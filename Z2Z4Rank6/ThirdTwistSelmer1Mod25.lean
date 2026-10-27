import Z2Z4Rank6.ThirdTwistSelmer1Mod27

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer1
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod25_00 : splitCoverResiduePossibleFor 25 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod25_01 : splitCoverResiduePossibleFor 25 r2 r3 (-34014894,195965994936994169,-207402551886)=true := by
  decide +kernel
theorem mod25_02 : splitCoverResiduePossibleFor 25 r2 r3 (1,34014894,34014894)=true := by
  decide +kernel
theorem mod25_03 : splitCoverResiduePossibleFor 25 r2 r3 (-34014894,207402551886,-195965994936994169)=true := by
  decide +kernel
def stage2 : List ECFullTriple := [(1,1,1),(-34014894,195965994936994169,-207402551886),(1,34014894,34014894),(-34014894,207402551886,-195965994936994169)]
theorem stage2_check : stage1.filter (splitCoverResiduePossibleFor 25 r2 r3)=stage2 := by
  rw [stage1_explicit]
  simp only [List.filter_cons,List.filter_nil,mod25_00,mod25_01,mod25_02,mod25_03]
  rfl
theorem stage2_explicit : stage2=[(1,1,1),(-34014894,195965994936994169,-207402551886),(1,34014894,34014894),(-34014894,207402551886,-195965994936994169)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer1
