module

public import Z2Z4Rank6.GTwistSelmerMod27

@[expose] public section

/-! Bounded exact mod 25 checks for h-covering candidates. -/
namespace Z2Z4Rank6.GTwistSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem hMod25_00 : splitCoverResiduePossibleFor 25 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem hMod25_01 : splitCoverResiduePossibleFor 25 r2 r3 (197637,1706268866918,77700126)=false := by
  decide +kernel
theorem hMod25_02 : splitCoverResiduePossibleFor 25 r2 r3 (-8067459,62944700679072065,-70220661315)=true := by
  decide +kernel
theorem hMod25_03 : splitCoverResiduePossibleFor 25 r2 r3 (30118681,28036769374369,23542647050209)=true := by
  decide +kernel
theorem hMod25_04 : splitCoverResiduePossibleFor 25 r2 r3 (165957,13254957782,18179777096094)=false := by
  decide +kernel
theorem hMod25_05 : splitCoverResiduePossibleFor 25 r2 r3 (-242981224101579,80526686585,-75435)=true := by
  decide +kernel
theorem hMod25_06 : splitCoverResiduePossibleFor 25 r2 r3 (-10670231,2773381737841,-1720740586319)=true := by
  decide +kernel
theorem hMod25_07 : splitCoverResiduePossibleFor 25 r2 r3 (86081651113029,390317112185,270165)=true := by
  decide +kernel
theorem hMod25_08 : splitCoverResiduePossibleFor 25 r2 r3 (-17428367307,19044929395521302,-65109557621346)=false := by
  decide +kernel
theorem hMod25_09 : splitCoverResiduePossibleFor 25 r2 r3 (-321373283685311,173854681,-90577319)=true := by
  decide +kernel
theorem hMod25_10 : splitCoverResiduePossibleFor 25 r2 r3 (2592665789826615394749,223331241983684841562985,129804066128973765)=true := by
  decide +kernel
theorem hMod25_11 : splitCoverResiduePossibleFor 25 r2 r3 (-14634706827,1394902262,-143629981613106)=false := by
  decide +kernel
theorem hMod25_12 : splitCoverResiduePossibleFor 25 r2 r3 (1,8067459,8067459)=true := by
  decide +kernel
theorem hMod25_13 : splitCoverResiduePossibleFor 25 r2 r3 (197637,8259081448002,41789146)=false := by
  decide +kernel
theorem hMod25_14 : splitCoverResiduePossibleFor 25 r2 r3 (-8067459,70220661315,-62944700679072065)=true := by
  decide +kernel
theorem hMod25_15 : splitCoverResiduePossibleFor 25 r2 r3 (30118681,226185487420177558371,189929339829032048931)=true := by
  decide +kernel
theorem hMod25_16 : splitCoverResiduePossibleFor 25 r2 r3 (165957,64159745298,9777556336474)=false := by
  decide +kernel
theorem hMod25_17 : splitCoverResiduePossibleFor 25 r2 r3 (-242981224101579,89835,-67618752185)=true := by
  decide +kernel
theorem hMod25_18 : splitCoverResiduePossibleFor 25 r2 r3 (-10670231,22374143461381016019,-13882004129764493421)=true := by
  decide +kernel
theorem hMod25_19 : splitCoverResiduePossibleFor 25 r2 r3 (86081651113029,435435,242171673415)=true := by
  decide +kernel
theorem hMod25_20 : splitCoverResiduePossibleFor 25 r2 r3 (-17428367307,92185719436570578,-35017611289766)=false := by
  decide +kernel
theorem hMod25_21 : splitCoverResiduePossibleFor 25 r2 r3 (-321373283685311,1402565510925579,-730728807362421)=true := by
  decide +kernel
theorem hMod25_22 : splitCoverResiduePossibleFor 25 r2 r3 (2592665789826615394749,249146748418946235,116354331280976062357015)=true := by
  decide +kernel
theorem hMod25_23 : splitCoverResiduePossibleFor 25 r2 r3 (-14634706827,6751932018,-77247934856726)=false := by
  decide +kernel

def hStageThird : List ECFullTriple := [(1,1,1),(-8067459,62944700679072065,-70220661315),(30118681,28036769374369,23542647050209),(-242981224101579,80526686585,-75435),(-10670231,2773381737841,-1720740586319),(86081651113029,390317112185,270165),(-321373283685311,173854681,-90577319),(2592665789826615394749,223331241983684841562985,129804066128973765),(1,8067459,8067459),(-8067459,70220661315,-62944700679072065),(30118681,226185487420177558371,189929339829032048931),(-242981224101579,89835,-67618752185),(-10670231,22374143461381016019,-13882004129764493421),(86081651113029,435435,242171673415),(-321373283685311,1402565510925579,-730728807362421),(2592665789826615394749,249146748418946235,116354331280976062357015)]

theorem hStageThird_check :
    hStageSecond.filter (splitCoverResiduePossibleFor 25 r2 r3)=hStageThird := by
  rw [hStageSecond_explicit]
  simp only [List.filter_cons,List.filter_nil,hMod25_00,hMod25_01,hMod25_02,hMod25_03,hMod25_04,hMod25_05,hMod25_06,hMod25_07,hMod25_08,hMod25_09,hMod25_10,hMod25_11,hMod25_12,hMod25_13,hMod25_14,hMod25_15,hMod25_16,hMod25_17,hMod25_18,hMod25_19,hMod25_20,hMod25_21,hMod25_22,hMod25_23]
  rfl

theorem hStageThird_explicit : hStageThird=[(1,1,1),(-8067459,62944700679072065,-70220661315),(30118681,28036769374369,23542647050209),(-242981224101579,80526686585,-75435),(-10670231,2773381737841,-1720740586319),(86081651113029,390317112185,270165),(-321373283685311,173854681,-90577319),(2592665789826615394749,223331241983684841562985,129804066128973765),(1,8067459,8067459),(-8067459,70220661315,-62944700679072065),(30118681,226185487420177558371,189929339829032048931),(-242981224101579,89835,-67618752185),(-10670231,22374143461381016019,-13882004129764493421),(86081651113029,435435,242171673415),(-321373283685311,1402565510925579,-730728807362421),(2592665789826615394749,249146748418946235,116354331280976062357015)] := rfl

end Z2Z4Rank6.GTwistSelmer
