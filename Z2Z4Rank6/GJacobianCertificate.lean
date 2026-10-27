import Z2Z4Rank6.GJacobianChecks
import Z2Z4Rank6.GJacobianSupport
import Z2Z4Rank6.GJacobianSurvivors
import Mathlib.Data.Set.Card

/-!
# Sixteen-class full local-solubility certificate for J_G

Canonical squarefree triples for roots 0,-9801,-2401 are exactly the sixteen
coverings with explicit global points. Source: Jaswal, Proposition 7.2(a),
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6

theorem gJacobian_fullTwoSelmerTriples :
    fullTwoSelmerTriples 9801 2401 = (gJacobianSurvivors.toFinset : Set ECFullTriple) := by
  ext d
  constructor
  · rintro ⟨hs1,hs2,hs3,hd1,hd2,hd3,hsq,hloc⟩
    norm_num at hd1 hd2 hd3
    have hm1 := gJacobian_squarefree_divisor_1 d.1 hs1 hd1
    have hm2 := gJacobian_squarefree_divisor_2 d.2.1 hs2 hd2
    have hm3 := gJacobian_squarefree_divisor_3 d.2.2 hs3 hd3
    have hblocks : d.2.1 ∈ (List.finRange 4).flatMap gJacobianBBlocks := by
      rw [gJacobianBBlocks_cover]
      exact hm2
    obtain ⟨j,hj,hb⟩ := List.mem_flatMap.mp hblocks
    have hraw : d ∈ gJacobianRawTriples := by
      apply List.mem_flatMap.mpr
      refine ⟨d.1,hm1,List.mem_flatMap.mpr ⟨j,hj,?_⟩⟩
      apply List.mem_flatMap.mpr
      refine ⟨d.2.1,hb,List.mem_map.mpr ⟨d.2.2,hm3,?_⟩⟩
      cases d
      rfl
    have hc : d ∈ gJacobianCandidates := by
      rw [←gJacobianCandidates_check]
      exact List.mem_filter.mpr ⟨hraw,(intSquareTest_iff _).2 hsq⟩
    have hr : d ∈ gJacobianRealCandidates := by
      by_cases hdpos : 0<d.2.1
      · rw [←gJacobianReal_check]
        exact List.mem_filter.mpr ⟨hc,by simpa using hdpos⟩
      · obtain ⟨hneg,hprod⟩ := gJacobianNegative_sign d hc hdpos
        have hR := hloc.1
        norm_num at hR
        exact (gJacobian_real_negative_obstruction (d.1 : ℝ) (d.2.1 : ℝ) (d.2.2 : ℝ)
          (by exact_mod_cast hneg) (by exact_mod_cast hprod) hR).elim
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    have h8 : d ∈ gJacobianStage8 := by
      rw [←gJacobianStage8_check]
      exact List.mem_filter.mpr ⟨hr,splitCover_local_implies_residue_test_for (p := 2) 3 d 9801 2401 (hloc.2 2)⟩
    have h3 : d ∈ gJacobianStage3 := by
      rw [←gJacobianStage3_check]
      refine List.mem_filter.mpr ⟨h8,?_⟩
      simp only [gJacobian_binary_good_of_local 3 d 9801 2401 hloc,Bool.not_false]
    have hl5 : SplitCoverEverywhereLocallySoluble (d.2.1,d.2.2,d.1) (-7400) (-9801) := by
      convert gJacobian_cycle_local d 9801 2401 hloc using 1; norm_num
    have h5 : d ∈ gJacobianStage5 := by
      rw [←gJacobianStage5_check]
      refine List.mem_filter.mpr ⟨h3,?_⟩
      simp only [gJacobian_binary_good_of_local 5 (d.2.1,d.2.2,d.1) (-7400) (-9801) hl5,Bool.not_false]
    have hl7 := gJacobian_swap_later_local d 9801 2401 hloc
    have h7 : d ∈ gJacobianSurvivors := by
      rw [←gJacobianStage7_check]
      refine List.mem_filter.mpr ⟨h5,?_⟩
      simp only [gJacobian_binary_good_of_local 7 (d.1,d.2.2,d.2.1) 2401 9801 hl7,Bool.not_false]
    simpa using h7
  · intro hd
    have hm : d ∈ gJacobianSurvivors := by simpa using hd
    obtain ⟨hs1,hs2,hs3,hd1,hd2,hd3,hsq⟩ := gJacobian_survivor_arithmetic d hm
    refine ⟨hs1,hs2,hs3,?_,?_,?_,hsq,gJacobian_survivor_locally_soluble d hm⟩ <;>
      norm_num <;> assumption

theorem gJacobian_fullTwoSelmerTriples_card : (fullTwoSelmerTriples 9801 2401).ncard=16 := by
  rw [gJacobian_fullTwoSelmerTriples,Set.ncard_coe_finset,gJacobianSurvivors_card]

end Z2Z4Rank6
