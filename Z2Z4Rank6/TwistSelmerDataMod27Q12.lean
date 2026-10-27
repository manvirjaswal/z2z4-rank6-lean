module

public import Z2Z4Rank6.TwistSelmerDataFilterQ12

@[expose] public section

/-! Independent bounded mod 27 checks. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem q12Mod27_00 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (1,1,1) = true := by decide +kernel
theorem q12Mod27_01 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (-69555786,130546930757070799,-67567197174) = true := by decide +kernel
theorem q12Mod27_02 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (14850238143924534,78180512382663227,32479792098) = false := by decide +kernel
theorem q12Mod27_03 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (1,69555786,69555786) = true := by decide +kernel
theorem q12Mod27_04 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (-69555786,67567197174,-130546930757070799) = true := by decide +kernel
theorem q12Mod27_05 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (14850238143924534,40463901102,62754374124804973) = false := by decide +kernel
theorem q12Mod27_06 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (-69555786,219634145,-5871707130) = false := by decide +kernel
theorem q12Mod27_07 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (-213501119,6599782683561896035,-5297550745631784965) = true := by decide +kernel
theorem q12Mod27_08 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (14850238143924534,131532085,2822550510) = true := by decide +kernel
theorem q12Mod27_09 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (-69555786,5871707130,-219634145) = false := by decide +kernel
theorem q12Mod27_10 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (-213501119,8887254321902327790,-7133671367221986210) = true := by decide +kernel
theorem q12Mod27_11 : splitCoverResiduePossibleFor 27 (r2 2) (r3 2)
    (14850238143924534,3516383490,105578915) = true := by decide +kernel

def q12StageSecond : List ECFullTriple := [(1,1,1),(-69555786,130546930757070799,-67567197174),(1,69555786,69555786),(-69555786,67567197174,-130546930757070799),(-213501119,6599782683561896035,-5297550745631784965),(14850238143924534,131532085,2822550510),(-213501119,8887254321902327790,-7133671367221986210),(14850238143924534,3516383490,105578915)]

theorem q12StageSecond_check :
    q12StageFirst.filter (splitCoverResiduePossibleFor 27 (r2 2) (r3 2))=q12StageSecond := by
  rw [q12StageFirst_explicit]
  simp only [List.filter_cons,List.filter_nil,q12Mod27_00,q12Mod27_01,q12Mod27_02,q12Mod27_03,q12Mod27_04,q12Mod27_05,q12Mod27_06,q12Mod27_07,q12Mod27_08,q12Mod27_09,q12Mod27_10,q12Mod27_11]
  rfl
end Z2Z4Rank6.TwistSelmer
