module

public import Z2Z4Rank6.ThirdTwistSelmer1Pool

@[expose] public section

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer1
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem mod16_00 : splitCoverResiduePossibleFor 16 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem mod16_01 : splitCoverResiduePossibleFor 16 r2 r3 (-6842662843,402509579,-17)=false := by
  decide +kernel
theorem mod16_02 : splitCoverResiduePossibleFor 16 r2 r3 (3964246,955369411139,963986)=false := by
  decide +kernel
theorem mod16_03 : splitCoverResiduePossibleFor 16 r2 r3 (-141187618,2001513045961,-16387762)=false := by
  decide +kernel
theorem mod16_04 : splitCoverResiduePossibleFor 16 r2 r3 (7177267383,10092785978561,3657567)=false := by
  decide +kernel
theorem mod16_05 : splitCoverResiduePossibleFor 16 r2 r3 (-175461,4194512179,-215151)=false := by
  decide +kernel
theorem mod16_06 : splitCoverResiduePossibleFor 16 r2 r3 (7242,2454263530651,3525843382062)=false := by
  decide +kernel
theorem mod16_07 : splitCoverResiduePossibleFor 16 r2 r3 (-34014894,195965994936994169,-207402551886)=true := by
  decide +kernel
theorem mod16_08 : splitCoverResiduePossibleFor 16 r2 r3 (158184296285,361856111521,61499285)=false := by
  decide +kernel
theorem mod16_09 : splitCoverResiduePossibleFor 16 r2 r3 (-3867095,899,-3617605)=false := by
  decide +kernel
theorem mod16_10 : splitCoverResiduePossibleFor 16 r2 r3 (3263884910,1799360228318939,59284449750010)=false := by
  decide +kernel
theorem mod16_11 : splitCoverResiduePossibleFor 16 r2 r3 (-15330115885370,858877100613961,-3487320573530)=false := by
  decide +kernel
theorem mod16_12 : splitCoverResiduePossibleFor 16 r2 r3 (4056195,4483788881,925483155)=false := by
  decide +kernel
theorem mod16_13 : splitCoverResiduePossibleFor 16 r2 r3 (-27755174810462385,10788840183979,-15733213635)=false := by
  decide +kernel
theorem mod16_14 : splitCoverResiduePossibleFor 16 r2 r3 (786334530,209480891139545491,892152804655830)=true := by
  decide +kernel
theorem mod16_15 : splitCoverResiduePossibleFor 16 r2 r3 (-28005501990,2623523084489,-15166597679149110)=false := by
  decide +kernel
theorem mod16_16 : splitCoverResiduePossibleFor 16 r2 r3 (1,34014894,34014894)=true := by
  decide +kernel
theorem mod16_17 : splitCoverResiduePossibleFor 16 r2 r3 (-6842662843,426,-578253198)=false := by
  decide +kernel
theorem mod16_18 : splitCoverResiduePossibleFor 16 r2 r3 (3964246,169141947546,8197470401871)=false := by
  decide +kernel
theorem mod16_19 : splitCoverResiduePossibleFor 16 r2 r3 (-141187618,406987369145214,-139356996831807)=false := by
  decide +kernel
theorem mod16_20 : splitCoverResiduePossibleFor 16 r2 r3 (7177267383,1786862188254,13823528200322)=false := by
  decide +kernel
theorem mod16_21 : splitCoverResiduePossibleFor 16 r2 r3 (-175461,852911491146,-813148717666)=false := by
  decide +kernel
theorem mod16_22 : splitCoverResiduePossibleFor 16 r2 r3 (7242,83481513843159515994,3331421913928900873)=false := by
  decide +kernel
theorem mod16_23 : splitCoverResiduePossibleFor 16 r2 r3 (-34014894,207402551886,-195965994936994169)=true := by
  decide +kernel
theorem mod16_24 : splitCoverResiduePossibleFor 16 r2 r3 (158184296285,382974,12505255590)=false := by
  decide +kernel
theorem mod16_25 : splitCoverResiduePossibleFor 16 r2 r3 (-3867095,30579389706,-735603270)=false := by
  decide +kernel
theorem mod16_26 : splitCoverResiduePossibleFor 16 r2 r3 (3263884910,365881644861547386,3013722828795435)=false := by
  decide +kernel
theorem mod16_27 : splitCoverResiduePossibleFor 16 r2 r3 (-15330115885370,152058610843854,-177277813458555)=false := by
  decide +kernel
theorem mod16_28 : splitCoverResiduePossibleFor 16 r2 r3 (4056195,911732973294,20909734330)=false := by
  decide +kernel
theorem mod16_29 : splitCoverResiduePossibleFor 16 r2 r3 (-27755174810462385,1910094063306,-355465483610)=false := by
  decide +kernel
theorem mod16_30 : splitCoverResiduePossibleFor 16 r2 r3 (786334530,221706176154,5039172789459845)=true := by
  decide +kernel
theorem mod16_31 : splitCoverResiduePossibleFor 16 r2 r3 (-28005501990,89238859625446379166,-85665937420817365)=false := by
  decide +kernel
def stage0 : List ECFullTriple := [(1,1,1),(-34014894,195965994936994169,-207402551886),(786334530,209480891139545491,892152804655830),(1,34014894,34014894),(-34014894,207402551886,-195965994936994169),(786334530,221706176154,5039172789459845)]
theorem stage0_check : rawPool.filter (splitCoverResiduePossibleFor 16 r2 r3)=stage0 := by
  rw [rawPool_explicit]
  simp only [List.filter_cons,List.filter_nil,mod16_00,mod16_01,mod16_02,mod16_03,mod16_04,mod16_05,mod16_06,mod16_07,mod16_08,mod16_09,mod16_10,mod16_11,mod16_12,mod16_13,mod16_14,mod16_15,mod16_16,mod16_17,mod16_18,mod16_19,mod16_20,mod16_21,mod16_22,mod16_23,mod16_24,mod16_25,mod16_26,mod16_27,mod16_28,mod16_29,mod16_30,mod16_31]
  rfl
theorem stage0_explicit : stage0=[(1,1,1),(-34014894,195965994936994169,-207402551886),(786334530,209480891139545491,892152804655830),(1,34014894,34014894),(-34014894,207402551886,-195965994936994169),(786334530,221706176154,5039172789459845)] := rfl

end Z2Z4Rank6.ThirdTwist.Selmer1
