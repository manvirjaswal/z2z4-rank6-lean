import Z2Z4Rank6.ECFullSelmerData
import Mathlib.Data.Nat.Squarefree

/-!
# Global points on the eight surviving full two-coverings

The points are explicit integer coordinates on the two homogeneous quadrics.
They certify local solubility at every place and agree with the Kummer span
of the point and torsion generators printed in Jaswal, Lemma 4.1(b),
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

theorem ecFull_survivor_points {K : Type*} [Field K] [CharZero K]
    (d : ECFullTriple) (hd : d ∈ ecFullSurvivors) :
    SplitCoverSoluble (d.1 : K) (d.2.1 : K) (d.2.2 : K) 729 484 := by
  simp only [ecFullSurvivors,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨![3,3,1,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![15,21,7,2],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![11,1,11,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![22,7,0,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![1,1,1,0],⟨0,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![1,7,7,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![6,15,4,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩
  · exact ⟨![3,21,7,1],⟨3,by norm_num⟩,by norm_num,by norm_num⟩

theorem ecFull_survivor_locally_soluble (d : ECFullTriple) (hd : d ∈ ecFullSurvivors) :
    SplitCoverEverywhereLocallySoluble d 729 484 := by
  constructor
  · simpa using (ecFull_survivor_points (K := ℝ) d hd)
  · intro p _
    simpa using (ecFull_survivor_points (K := ℚ_[p]) d hd)

theorem ecFull_survivor_arithmetic (d : ECFullTriple) (hd : d ∈ ecFullSurvivors) :
    Squarefree d.1 ∧ Squarefree d.2.1 ∧ Squarefree d.2.2 ∧
    d.1 ∣ 352836 ∧ d.2.1 ∣ 178605 ∧ d.2.2 ∣ 118580 ∧
    IsSquare (d.1*d.2.1*d.2.2) := by
  simp only [ecFullSurvivors,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  all_goals simp only [←Int.squarefree_natAbs]
  all_goals decide +kernel

end Z2Z4Rank6
