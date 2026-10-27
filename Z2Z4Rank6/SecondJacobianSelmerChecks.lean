import Z2Z4Rank6.SecondJacobianSelmerCheck0
import Z2Z4Rank6.SecondJacobianSelmerCheck1
import Z2Z4Rank6.SecondJacobianSelmerCheck2
import Z2Z4Rank6.SecondJacobianSelmerCheck3
import Z2Z4Rank6.SecondJacobianSelmerCheck4
import Z2Z4Rank6.SecondJacobianSelmerCheck5
import Z2Z4Rank6.SecondJacobianSelmerCheck6
import Z2Z4Rank6.SecondJacobianSelmerCheck7
import Z2Z4Rank6.SecondJacobianSelmerSupport

namespace Z2Z4Rank6.SecondJacobianSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem block_check (j : Fin 8) : (rawBlock j).filter pairGood=survivorBlocks j := by
  fin_cases j
  · exact block_check_0
  · exact block_check_1
  · exact block_check_2
  · exact block_check_3
  · exact block_check_4
  · exact block_check_5
  · exact block_check_6
  · exact block_check_7

theorem aBlocks_cover : (List.finRange 8).flatMap aBlocks=signed1 := by decide +kernel

theorem survivorBlocks_cover : (List.finRange 8).flatMap survivorBlocks=survivors := by
  decide +kernel

theorem survivors_card : survivors.toFinset.card=16 := by decide +kernel

/-- Every covering's first two squarefree coefficients occur in the
kernel-checked list. The third coefficient need not be normalized by a gcd. -/
theorem covering_pair_mem (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples A B) :
    (d.1,d.2.1)∈survivors := by
  obtain ⟨ha,hb⟩ := support_lists d hd
  rw [←aBlocks_cover,List.mem_flatMap] at ha
  obtain ⟨j,hj,ha⟩ := ha
  have hr : (d.1,d.2.1)∈rawBlock j := by
    apply List.mem_flatMap.mpr
    exact ⟨d.1,ha,List.mem_map.mpr ⟨d.2.1,hb,rfl⟩⟩
  have hg : pairGood (d.1,d.2.1)=true := by
    exact decide_eq_true (And.intro (necessary_sharedParity d hd) (necessary_pair_tests d hd))
  have hm : (d.1,d.2.1)∈survivorBlocks j := by
    rw [←block_check j]
    exact List.mem_filter.mpr ⟨hr,hg⟩
  rw [←survivorBlocks_cover,List.mem_flatMap]
  exact ⟨j,hj,hm⟩

noncomputable def pairClass (d : ℤ×ℤ) : RatSquareClassAdd×RatSquareClassAdd :=
  (squareClass (d.1:ℚ),squareClass (d.2:ℚ))

theorem classes_subset : fullTwoSelmerClasses A B ⊆
    pairClass '' (survivors.toFinset:Set (ℤ×ℤ)) := by
  rintro q ⟨d,hd,rfl⟩
  exact ⟨(d.1,d.2.1),by simpa using covering_pair_mem d hd,rfl⟩

theorem classes_finite : (fullTwoSelmerClasses A B).Finite :=
  ((Finset.finite_toSet survivors.toFinset).image pairClass).subset classes_subset

theorem classes_card_le : (fullTwoSelmerClasses A B).ncard≤16 := by
  calc
    _ ≤ (pairClass '' (survivors.toFinset:Set (ℤ×ℤ))).ncard :=
      Set.ncard_le_ncard classes_subset ((Finset.finite_toSet _).image pairClass)
    _ ≤ (survivors.toFinset:Set (ℤ×ℤ)).ncard :=
      Set.ncard_image_le (Finset.finite_toSet _)
    _ = 16 := by rw [Set.ncard_coe_finset,survivors_card]

end Z2Z4Rank6.SecondJacobianSelmer
