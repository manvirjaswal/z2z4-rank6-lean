module

public import Z2Z4Rank6.GJacobianCandidateChunks
public import Z2Z4Rank6.GJacobianSieve

@[expose] public section

/-! Assembly of exact finite candidate and local checks for J_G. -/
namespace Z2Z4Rank6
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem gJacobianBBlocks_cover :
    (List.finRange 4).flatMap gJacobianBBlocks = gJacobianD2 := by decide +kernel

theorem gJacobianCandidates_check :
    gJacobianRawTriples.filter (fun d => intSquareTest (d.1*d.2.1*d.2.2)) =
      gJacobianCandidates := by
  simp only [gJacobianRawTriples,List.filter_flatMap]
  calc
    gJacobianD1.flatMap (fun a => (List.finRange 4).flatMap (fun j =>
      (gJacobianRawChunk a j).filter (fun d => intSquareTest (d.1*d.2.1*d.2.2)))) =
      gJacobianD1.flatMap (fun a => (List.finRange 4).flatMap (gJacobianResultChunk a)) := by
        apply List.flatMap_congr
        intro a ha
        apply List.flatMap_congr
        intro j _
        exact gJacobianCandidate_chunks a ha j
    _ = gJacobianCandidates := by decide +kernel

theorem gJacobianReal_check :
    gJacobianCandidates.filter (fun d => decide (0<d.2.1)) = gJacobianRealCandidates := by
  decide +kernel

theorem gJacobianNegative_sign (d : ECFullTriple) (hd : d ∈ gJacobianCandidates)
    (hn : ¬0<d.2.1) : d.2.1<0 ∧ d.1*d.2.2<0 := by
  have ht : ∀ d ∈ gJacobianCandidates, ¬0<d.2.1 → d.2.1<0 ∧ d.1*d.2.2<0 := by
    decide +kernel
  exact ht d hd hn

theorem gJacobianStage8_check :
    gJacobianRealCandidates.filter (splitCoverResiduePossibleFor 8 9801 2401) = gJacobianStage8 := by
  decide +kernel

local instance gJacobianChecksPrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance gJacobianChecksPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance gJacobianChecksPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem gJacobianStage3_check :
    gJacobianStage8.filter (fun d => !(gJacobianBinaryBad 3 d 9801 2401)) = gJacobianStage3 := by
  decide +kernel

theorem gJacobianStage5_check :
    gJacobianStage3.filter (fun d => !(gJacobianBinaryBad 5 (d.2.1,d.2.2,d.1) (-7400) (-9801))) =
      gJacobianStage5 := by
  decide +kernel

theorem gJacobianStage7_check :
    gJacobianStage5.filter (fun d => !(gJacobianBinaryBad 7 (d.1,d.2.2,d.2.1) 2401 9801)) =
      gJacobianSurvivors := by
  decide +kernel

theorem gJacobianSurvivors_card : gJacobianSurvivors.toFinset.card=16 := by decide +kernel

end Z2Z4Rank6
