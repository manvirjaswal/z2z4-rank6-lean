import Z2Z4Rank6.GTwistSelmerFilter

/-! Bounded exact mod 27 checks for h-covering candidates. -/
namespace Z2Z4Rank6.GTwistSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem hMod27_00 : splitCoverResiduePossibleFor 27 r2 r3 (1,1,1)=true := by
  decide +kernel
theorem hMod27_01 : splitCoverResiduePossibleFor 27 r2 r3 (197637,1706268866918,77700126)=true := by
  decide +kernel
theorem hMod27_02 : splitCoverResiduePossibleFor 27 r2 r3 (-8067459,62944700679072065,-70220661315)=true := by
  decide +kernel
theorem hMod27_03 : splitCoverResiduePossibleFor 27 r2 r3 (-36990910317647,17902179117763655,-23103637507190665)=false := by
  decide +kernel
theorem hMod27_04 : splitCoverResiduePossibleFor 27 r2 r3 (41266797,60467407,145095531)=false := by
  decide +kernel
theorem hMod27_05 : splitCoverResiduePossibleFor 27 r2 r3 (-60419607788833059,73760377209610,-874197789891760110)=false := by
  decide +kernel
theorem hMod27_06 : splitCoverResiduePossibleFor 27 r2 r3 (30118681,28036769374369,23542647050209)=true := by
  decide +kernel
theorem hMod27_07 : splitCoverResiduePossibleFor 27 r2 r3 (165957,13254957782,18179777096094)=true := by
  decide +kernel
theorem hMod27_08 : splitCoverResiduePossibleFor 27 r2 r3 (-242981224101579,80526686585,-75435)=true := by
  decide +kernel
theorem hMod27_09 : splitCoverResiduePossibleFor 27 r2 r3 (-97311330924693743,1122231965855,-106222585)=false := by
  decide +kernel
theorem hMod27_10 : splitCoverResiduePossibleFor 27 r2 r3 (108559830093,34598178463777667167,6088996053296979)=false := by
  decide +kernel
theorem hMod27_11 : splitCoverResiduePossibleFor 27 r2 r3 (-4431366486651,5402410,-168438943643790)=false := by
  decide +kernel
theorem hMod27_12 : splitCoverResiduePossibleFor 27 r2 r3 (23882367793,6455,92495615)=false := by
  decide +kernel
theorem hMod27_13 : splitCoverResiduePossibleFor 27 r2 r3 (4720039523505141,6608322490,7186920939947490)=false := by
  decide +kernel
theorem hMod27_14 : splitCoverResiduePossibleFor 27 r2 r3 (-26643,9751309167943,-259804130161505349)=false := by
  decide +kernel
theorem hMod27_15 : splitCoverResiduePossibleFor 27 r2 r3 (-10670231,2773381737841,-1720740586319)=true := by
  decide +kernel
theorem hMod27_16 : splitCoverResiduePossibleFor 27 r2 r3 (86081651113029,390317112185,270165)=true := by
  decide +kernel
theorem hMod27_17 : splitCoverResiduePossibleFor 27 r2 r3 (-17428367307,19044929395521302,-65109557621346)=true := by
  decide +kernel
theorem hMod27_18 : splitCoverResiduePossibleFor 27 r2 r3 (62826920873617,180977346311551895,190199285320728215)=false := by
  decide +kernel
theorem hMod27_19 : splitCoverResiduePossibleFor 27 r2 r3 (346182733149,51336010,146873059923672690)=false := by
  decide +kernel
theorem hMod27_20 : splitCoverResiduePossibleFor 27 r2 r3 (-70089267,12475087,-24377349)=false := by
  decide +kernel
theorem hMod27_21 : splitCoverResiduePossibleFor 27 r2 r3 (-321373283685311,173854681,-90577319)=true := by
  decide +kernel
theorem hMod27_22 : splitCoverResiduePossibleFor 27 r2 r3 (2592665789826615394749,223331241983684841562985,129804066128973765)=true := by
  decide +kernel
theorem hMod27_23 : splitCoverResiduePossibleFor 27 r2 r3 (-14634706827,1394902262,-143629981613106)=true := by
  decide +kernel
theorem hMod27_24 : splitCoverResiduePossibleFor 27 r2 r3 (1,8067459,8067459)=true := by
  decide +kernel
theorem hMod27_25 : splitCoverResiduePossibleFor 27 r2 r3 (197637,8259081448002,41789146)=true := by
  decide +kernel
theorem hMod27_26 : splitCoverResiduePossibleFor 27 r2 r3 (-8067459,70220661315,-62944700679072065)=true := by
  decide +kernel
theorem hMod27_27 : splitCoverResiduePossibleFor 27 r2 r3 (-36990910317647,86654312398842045,-42957459464882115)=false := by
  decide +kernel
theorem hMod27_28 : splitCoverResiduePossibleFor 27 r2 r3 (41266797,112429317,29975729)=false := by
  decide +kernel
theorem hMod27_29 : splitCoverResiduePossibleFor 27 r2 r3 (-60419607788833059,595058818963063080990,-108360983290)=false := by
  decide +kernel
theorem hMod27_30 : splitCoverResiduePossibleFor 27 r2 r3 (30118681,226185487420177558371,189929339829032048931)=true := by
  decide +kernel
theorem hMod27_31 : splitCoverResiduePossibleFor 27 r2 r3 (165957,64159745298,9777556336474)=true := by
  decide +kernel
theorem hMod27_32 : splitCoverResiduePossibleFor 27 r2 r3 (-242981224101579,89835,-67618752185)=true := by
  decide +kernel
theorem hMod27_33 : splitCoverResiduePossibleFor 27 r2 r3 (-97311330924693743,5432089507845,-197503635)=false := by
  decide +kernel
theorem hMod27_34 : splitCoverResiduePossibleFor 27 r2 r3 (108559830093,64329690441771917877,1257944295856361)=false := by
  decide +kernel
theorem hMod27_35 : splitCoverResiduePossibleFor 27 r2 r3 (-4431366486651,43583721176190,-20878810)=false := by
  decide +kernel
theorem hMod27_36 : splitCoverResiduePossibleFor 27 r2 r3 (23882367793,31245,171980565)=false := by
  decide +kernel
theorem hMod27_37 : splitCoverResiduePossibleFor 27 r2 r3 (4720039523505141,53312370746852910,890853110)=false := by
  decide +kernel
theorem hMod27_38 : splitCoverResiduePossibleFor 27 r2 r3 (-26643,18130974751533,-53673728922788191)=false := by
  decide +kernel
theorem hMod27_39 : splitCoverResiduePossibleFor 27 r2 r3 (-10670231,22374143461381016019,-13882004129764493421)=true := by
  decide +kernel
theorem hMod27_40 : splitCoverResiduePossibleFor 27 r2 r3 (86081651113029,435435,242171673415)=true := by
  decide +kernel
theorem hMod27_41 : splitCoverResiduePossibleFor 27 r2 r3 (-17428367307,92185719436570578,-35017611289766)=true := by
  decide +kernel
theorem hMod27_42 : splitCoverResiduePossibleFor 27 r2 r3 (62826920873617,876008859102159405,353644662528651165)=false := by
  decide +kernel
theorem hMod27_43 : splitCoverResiduePossibleFor 27 r2 r3 (346182733149,414151155898590,18205615910)=false := by
  decide +kernel
theorem hMod27_44 : splitCoverResiduePossibleFor 27 r2 r3 (-70089267,23195397,-5036191)=false := by
  decide +kernel
theorem hMod27_45 : splitCoverResiduePossibleFor 27 r2 r3 (-321373283685311,1402565510925579,-730728807362421)=true := by
  decide +kernel
theorem hMod27_46 : splitCoverResiduePossibleFor 27 r2 r3 (2592665789826615394749,249146748418946235,116354331280976062357015)=true := by
  decide +kernel
theorem hMod27_47 : splitCoverResiduePossibleFor 27 r2 r3 (-14634706827,6751932018,-77247934856726)=true := by
  decide +kernel

def hStageSecond : List ECFullTriple := [(1,1,1),(197637,1706268866918,77700126),(-8067459,62944700679072065,-70220661315),(30118681,28036769374369,23542647050209),(165957,13254957782,18179777096094),(-242981224101579,80526686585,-75435),(-10670231,2773381737841,-1720740586319),(86081651113029,390317112185,270165),(-17428367307,19044929395521302,-65109557621346),(-321373283685311,173854681,-90577319),(2592665789826615394749,223331241983684841562985,129804066128973765),(-14634706827,1394902262,-143629981613106),(1,8067459,8067459),(197637,8259081448002,41789146),(-8067459,70220661315,-62944700679072065),(30118681,226185487420177558371,189929339829032048931),(165957,64159745298,9777556336474),(-242981224101579,89835,-67618752185),(-10670231,22374143461381016019,-13882004129764493421),(86081651113029,435435,242171673415),(-17428367307,92185719436570578,-35017611289766),(-321373283685311,1402565510925579,-730728807362421),(2592665789826615394749,249146748418946235,116354331280976062357015),(-14634706827,6751932018,-77247934856726)]

theorem hStageSecond_check :
    hStageFirst.filter (splitCoverResiduePossibleFor 27 r2 r3)=hStageSecond := by
  rw [hStageFirst_explicit]
  simp only [List.filter_cons,List.filter_nil,hMod27_00,hMod27_01,hMod27_02,hMod27_03,hMod27_04,hMod27_05,hMod27_06,hMod27_07,hMod27_08,hMod27_09,hMod27_10,hMod27_11,hMod27_12,hMod27_13,hMod27_14,hMod27_15,hMod27_16,hMod27_17,hMod27_18,hMod27_19,hMod27_20,hMod27_21,hMod27_22,hMod27_23,hMod27_24,hMod27_25,hMod27_26,hMod27_27,hMod27_28,hMod27_29,hMod27_30,hMod27_31,hMod27_32,hMod27_33,hMod27_34,hMod27_35,hMod27_36,hMod27_37,hMod27_38,hMod27_39,hMod27_40,hMod27_41,hMod27_42,hMod27_43,hMod27_44,hMod27_45,hMod27_46,hMod27_47]
  rfl

theorem hStageSecond_explicit : hStageSecond=[(1,1,1),(197637,1706268866918,77700126),(-8067459,62944700679072065,-70220661315),(30118681,28036769374369,23542647050209),(165957,13254957782,18179777096094),(-242981224101579,80526686585,-75435),(-10670231,2773381737841,-1720740586319),(86081651113029,390317112185,270165),(-17428367307,19044929395521302,-65109557621346),(-321373283685311,173854681,-90577319),(2592665789826615394749,223331241983684841562985,129804066128973765),(-14634706827,1394902262,-143629981613106),(1,8067459,8067459),(197637,8259081448002,41789146),(-8067459,70220661315,-62944700679072065),(30118681,226185487420177558371,189929339829032048931),(165957,64159745298,9777556336474),(-242981224101579,89835,-67618752185),(-10670231,22374143461381016019,-13882004129764493421),(86081651113029,435435,242171673415),(-17428367307,92185719436570578,-35017611289766),(-321373283685311,1402565510925579,-730728807362421),(2592665789826615394749,249146748418946235,116354331280976062357015),(-14634706827,6751932018,-77247934856726)] := rfl

end Z2Z4Rank6.GTwistSelmer
