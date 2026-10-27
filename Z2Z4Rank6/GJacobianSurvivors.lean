import Z2Z4Rank6.GJacobianData
import Z2Z4Rank6.ECSquarefreeCoordinates
import Mathlib.Data.Nat.Squarefree
/-! Exact global covering points for all 16 survivors. -/
namespace Z2Z4Rank6
theorem gJacobian_survivor_points {K:Type*}[Field K][CharZero K]
    (d:ECFullTriple) (hd:d∈gJacobianSurvivors):
    SplitCoverSoluble (d.1:K) (d.2.1:K) (d.2.2:K) 9801 2401 := by
  simp only [gJacobianSurvivors,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨![6,3,13,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![21,3,7,4],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![21,6,14,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![19,2,2,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![21,15,35,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![161,25,35,9],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![51,60,10,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![49,10,0,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![1,1,1,0],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![294,51,49,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![35,46,126,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![21,6,14,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![7,19,7,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![3,3,1,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![3,6,8,1],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![21,12,14,13],⟨0,by norm_num⟩,by norm_num,by norm_num⟩

theorem gJacobian_survivor_locally_soluble (d:ECFullTriple) (hd:d∈gJacobianSurvivors):
    SplitCoverEverywhereLocallySoluble d 9801 2401 :=
  splitCover_global_implies_everywhere d 9801 2401 (gJacobian_survivor_points d hd)
theorem gJacobian_survivor_arithmetic (d:ECFullTriple) (hd:d∈gJacobianSurvivors):
    Squarefree d.1 ∧ Squarefree d.2.1 ∧ Squarefree d.2.2 ∧
    d.1∣23532201 ∧ d.2.1∣72527400 ∧ d.2.2∣17767400 ∧ IsSquare (d.1*d.2.1*d.2.2) := by
  simp only [gJacobianSurvivors,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  all_goals simp only [←Int.squarefree_natAbs]
  all_goals decide +kernel
end Z2Z4Rank6
