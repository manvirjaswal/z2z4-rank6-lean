import Z2Z4Rank6.TwistSelmerDataFilterQ1

/-! Independent bounded mod 27 checks. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem q1Mod27_00 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (1,1,1) = true := by decide +kernel
theorem q1Mod27_01 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (4301130,1727983365,33032360403122) = false := by decide +kernel
theorem q1Mod27_02 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-13830,371746821257,-24191767110) = true := by decide +kernel
theorem q1Mod27_03 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-16458431,924852207,-657642777) = false := by decide +kernel
theorem q1Mod27_04 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (227620100730,83731360839,91492509030230) = false := by decide +kernel
theorem q1Mod27_05 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-731897430,9190513653995,-54698754) = true := by decide +kernel
theorem q1Mod27_06 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (78595609,6163050332679,16753823082159) = true := by decide +kernel
theorem q1Mod27_07 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (3495103770,1722763915,39198) = false := by decide +kernel
theorem q1Mod27_08 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-1086977272470,15695463,-65564992010) = true := by decide +kernel
theorem q1Mod27_09 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-166991,37209241793,-59557826647) = false := by decide +kernel
theorem q1Mod27_10 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (2309485530,1042321,108570) = false := by decide +kernel
theorem q1Mod27_11 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-718249999830,4845,-148245614) = true := by decide +kernel
theorem q1Mod27_12 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (1,13830,13830) = true := by decide +kernel
theorem q1Mod27_13 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (4301130,106213377502,537402826515) = false := by decide +kernel
theorem q1Mod27_14 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-13830,24191767110,-371746821257) = true := by decide +kernel
theorem q1Mod27_15 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-16458431,6687290,-4755190) = false := by decide +kernel
theorem q1Mod27_16 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (227620100730,128667191155930,59539593729) = false := by decide +kernel
theorem q1Mod27_17 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-731897430,23923245954,-21013437995) = true := by decide +kernel
theorem q1Mod27_18 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (78595609,44562909130,121141164730) = true := by decide +kernel
theorem q1Mod27_19 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (3495103770,4484418,15058565) = false := by decide +kernel
theorem q1Mod27_20 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-1086977272470,24118694810,-42667023) = true := by decide +kernel
theorem q1Mod27_21 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-166991,514603813997190,-823684742528010) = false := by decide +kernel
theorem q1Mod27_22 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (2309485530,67830,1668359) = false := by decide +kernel
theorem q1Mod27_23 : splitCoverResiduePossibleFor 27 (r2 0) (r3 0)
    (-718249999830,297806,-2411805) = true := by decide +kernel

def q1StageSecond : List ECFullTriple := [(1,1,1),(-13830,371746821257,-24191767110),(-731897430,9190513653995,-54698754),(78595609,6163050332679,16753823082159),(-1086977272470,15695463,-65564992010),(-718249999830,4845,-148245614),(1,13830,13830),(-13830,24191767110,-371746821257),(-731897430,23923245954,-21013437995),(78595609,44562909130,121141164730),(-1086977272470,24118694810,-42667023),(-718249999830,297806,-2411805)]

theorem q1StageSecond_check :
    q1StageFirst.filter (splitCoverResiduePossibleFor 27 (r2 0) (r3 0))=q1StageSecond := by
  rw [q1StageFirst_explicit]
  simp only [List.filter_cons,List.filter_nil,q1Mod27_00,q1Mod27_01,q1Mod27_02,q1Mod27_03,q1Mod27_04,q1Mod27_05,q1Mod27_06,q1Mod27_07,q1Mod27_08,q1Mod27_09,q1Mod27_10,q1Mod27_11,q1Mod27_12,q1Mod27_13,q1Mod27_14,q1Mod27_15,q1Mod27_16,q1Mod27_17,q1Mod27_18,q1Mod27_19,q1Mod27_20,q1Mod27_21,q1Mod27_22,q1Mod27_23]
  rfl
end Z2Z4Rank6.TwistSelmer
