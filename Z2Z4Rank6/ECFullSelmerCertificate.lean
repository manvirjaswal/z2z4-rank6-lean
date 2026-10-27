import Z2Z4Rank6.ECFullSelmerChecks
import Z2Z4Rank6.ECFullSelmerSupport
import Z2Z4Rank6.ECFullSelmerLocal
import Z2Z4Rank6.ECFullSelmerReal
import Z2Z4Rank6.ECFullSelmerSurvivors
import Mathlib.Data.Set.Card

/-!
# Exact eight-class full two-descent certificate for E_C

The canonical squarefree triples whose intersections of quadrics are
soluble over every completion are exactly the eight checked survivors.
Their cardinality is therefore 8. This is the explicit split full two-Selmer
model underlying the dimension 3 computation in Jaswal, Lemma 4.1(b),
DOI 10.5281/zenodo.23437117; the generic identification with the cohomological
Selmer group belongs to the published two-descent theory.
-/

namespace Z2Z4Rank6

theorem ec_fullTwoSelmerTriples :
    fullTwoSelmerTriples 729 484 = (ecFullSurvivors.toFinset : Set ECFullTriple) := by
  ext d
  constructor
  · rintro ⟨hs1,hs2,hs3,hd1,hd2,hd3,hsq,hloc⟩
    norm_num at hd1 hd2 hd3
    have hm1 := ec_squarefree_divisor_mem d.1 hs1 hd1
    have hm2 := ecFull_second_squarefree_divisor_mem d.2.1 hs2 hd2
    have hm3 := ecFull_third_squarefree_divisor_mem d.2.2 hs3 hd3
    have hraw : d ∈ ecFullRawTriples := by
      apply List.mem_flatMap.mpr
      refine ⟨d.1,hm1,List.mem_flatMap.mpr ⟨d.2.1,hm2,List.mem_map.mpr ⟨d.2.2,hm3,?_⟩⟩⟩
      cases d
      rfl
    have hc : d ∈ ecFullCandidates := by
      rw [←ecFullCandidates_check]
      exact List.mem_filter.mpr ⟨hraw,(intSquareTest_iff _).2 hsq⟩
    have hr : d ∈ ecFullRealCandidates := by
      by_cases hdpos : 0<d.2.1
      · rw [←ecFullRealCandidates_check]
        exact List.mem_filter.mpr ⟨hc,by simpa using hdpos⟩
      · obtain ⟨hneg,hprod⟩ := ecFullNegativeCandidates_sign d hc hdpos
        have hR := hloc.1
        norm_num at hR
        exact (splitCover_real_negative_obstruction (d.1 : ℝ) (d.2.1 : ℝ) (d.2.2 : ℝ)
          (by exact_mod_cast hneg) (by exact_mod_cast hprod) hR).elim
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hL2 := hloc.2 2
    have hL3 := hloc.2 3
    have hL5 := hloc.2 5
    norm_num at hL2 hL3 hL5
    have h8 : d ∈ ecFullStage8 := by
      rw [←ecFullStage8_check]
      exact List.mem_filter.mpr ⟨hr,splitCover_local_implies_residue_test (p := 2) 3 d hL2⟩
    have h9 : d ∈ ecFullStage9 := by
      rw [←ecFullStage9_check]
      exact List.mem_filter.mpr ⟨h8,splitCover_local_implies_residue_test (p := 3) 2 d hL3⟩
    have h25 : d ∈ ecFullSurvivors := by
      rw [←ecFullStage25_check]
      exact List.mem_filter.mpr ⟨h9,splitCover_local_implies_residue_test (p := 5) 2 d hL5⟩
    simpa using h25
  · intro hd
    have hm : d ∈ ecFullSurvivors := by simpa using hd
    obtain ⟨hs1,hs2,hs3,hd1,hd2,hd3,hsq⟩ := ecFull_survivor_arithmetic d hm
    refine ⟨hs1,hs2,hs3,?_,?_,?_,hsq,ecFull_survivor_locally_soluble d hm⟩ <;>
      norm_num <;> assumption

theorem ec_fullTwoSelmerTriples_card : (fullTwoSelmerTriples 729 484).ncard = 8 := by
  rw [ec_fullTwoSelmerTriples,Set.ncard_coe_finset,ecFullSurvivors_card]

end Z2Z4Rank6
