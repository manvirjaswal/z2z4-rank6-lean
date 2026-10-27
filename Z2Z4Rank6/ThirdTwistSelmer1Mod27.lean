import Z2Z4Rank6.ThirdTwistSelmer1Mod16

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer1
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod27_00 : splitCoverResiduePossibleFor 27 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod27_01 : splitCoverResiduePossibleFor 27 r2 r3 (-34014894,195965994936994169,-207402551886)=true := by
  decide +kernel
theorem mod27_02 : splitCoverResiduePossibleFor 27 r2 r3 (786334530,209480891139545491,892152804655830)=false := by
  decide +kernel
theorem mod27_03 : splitCoverResiduePossibleFor 27 r2 r3 (1,34014894,34014894)=true := by
  decide +kernel
theorem mod27_04 : splitCoverResiduePossibleFor 27 r2 r3 (-34014894,207402551886,-195965994936994169)=true := by
  decide +kernel
theorem mod27_05 : splitCoverResiduePossibleFor 27 r2 r3 (786334530,221706176154,5039172789459845)=false := by
  decide +kernel
def stage1 : List ECFullTriple := [(1,1,1),(-34014894,195965994936994169,-207402551886),(1,34014894,34014894),(-34014894,207402551886,-195965994936994169)]
theorem stage1_check : stage0.filter (splitCoverResiduePossibleFor 27 r2 r3)=stage1 := by
  rw [stage0_explicit]
  simp only [List.filter_cons,List.filter_nil,mod27_00,mod27_01,mod27_02,mod27_03,mod27_04,mod27_05]
  rfl
theorem stage1_explicit : stage1=[(1,1,1),(-34014894,195965994936994169,-207402551886),(1,34014894,34014894),(-34014894,207402551886,-195965994936994169)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer1
