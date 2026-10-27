module

public import Z2Z4Rank6.TwistSelmerDataSourceQ1
public import Z2Z4Rank6.TwistSelmerDataSourceQ2
public import Z2Z4Rank6.TwistSelmerDataSourceQ12
public import Z2Z4Rank6.TwistSelmerSurvivors

@[expose] public section

/-!
# Proved eight-class bounds for the three twist fibers

The support, local characters, matrix identities, exhaustive decoding and
small residue checks imply that every canonical locally soluble covering
is one of eight explicit triples. Consequently every complete
rational two-descent image has at most eight elements.

This proves the concrete upper-bound input in Proposition 5.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117.
The source point groups and squareclass groups are the Mathlib ones.
-/

namespace Z2Z4Rank6.TwistSelmer

noncomputable section

theorem q2FullCover_mem_survivors (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 1) (r3 1)) : d∈q2SurvivorList :=
  q2FullCover_mem_stageFirst d hd

theorem q12FullCover_mem_survivors (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 2) (r3 2)) : d∈q12SurvivorList := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp := q12FullCover_mem_stageFirst d hd
  have ht := splitCover_local_implies_residue_test_for (p:=3) 3 d (r2 2) (r3 2)
    (hd.2.2.2.2.2.2.2.2 3)
  have hm : d∈q12StageFirst.filter (splitCoverResiduePossibleFor 27 (r2 2) (r3 2)) :=
    List.mem_filter.mpr ⟨hp,ht⟩
  rwa [q12StageSecond_check] at hm

theorem q1FullCover_mem_stageSecond (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 0) (r3 0)) : d∈q1StageSecond := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp := q1FullCover_mem_stageFirst d hd
  have ht := splitCover_local_implies_residue_test_for (p:=3) 3 d (r2 0) (r3 0)
    (hd.2.2.2.2.2.2.2.2 3)
  have hm : d∈q1StageFirst.filter (splitCoverResiduePossibleFor 27 (r2 0) (r3 0)) :=
    List.mem_filter.mpr ⟨hp,ht⟩
  rwa [q1StageSecond_check] at hm

theorem q1FullCover_mem_survivors (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 0) (r3 0)) : d∈q1SurvivorList := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp := q1FullCover_mem_stageSecond d hd
  have ht := highDifferenceTest_of_mem (p:=5) q1HighS (r2 0) (r3 0)
    q1HighDifference_identity d hd
  have hm : d∈q1StageSecond.filter (highDifferenceTest 5 q1HighS) :=
    List.mem_filter.mpr ⟨hp,ht⟩
  rwa [q1HighDifference_filter_eq] at hm

/-- The locally soluble covering triples are contained in the eight
explicit survivors in each of the three normalized rational twist fibers. -/
theorem fullTwoSelmerTriples_subset_survivors (k : Fin 3) :
    fullTwoSelmerTriples (r2 k) (r3 k) ⊆ (survivors k : Set ECFullTriple) := by
  fin_cases k
  · intro d hd
    change d∈q1SurvivorList.toFinset
    exact List.mem_toFinset.mpr (q1FullCover_mem_survivors d hd)
  · intro d hd
    change d∈q2SurvivorList.toFinset
    exact List.mem_toFinset.mpr (q2FullCover_mem_survivors d hd)
  · intro d hd
    change d∈q12SurvivorList.toFinset
    exact List.mem_toFinset.mpr (q12FullCover_mem_survivors d hd)

/-- The explicit full split two-Selmer squareclass model has at most eight
classes for each normalized twist fiber. -/
theorem fullTwoSelmerClasses_card_le_eight (k : Fin 3) :
    (fullTwoSelmerClasses (r2 k) (r3 k)).ncard≤8 := by
  have hf : (fullTwoSelmerTriples (r2 k) (r3 k)).Finite :=
    (survivors k).finite_toSet.subset (fullTwoSelmerTriples_subset_survivors k)
  calc
    _≤(fullTwoSelmerTriples (r2 k) (r3 k)).ncard := Set.ncard_image_le hf
    _≤(survivors k : Set ECFullTriple).ncard :=
      Set.ncard_le_ncard (fullTwoSelmerTriples_subset_survivors k) (survivors k).finite_toSet
    _=8 := by rw [Set.ncard_coe_finset,survivors_card]

/-- Every complete two-descent homomorphism on a normalized twist
fiber has finite image of cardinality at most eight. The coordinate property is the published
descent-map setup. -/
theorem descent_image_card_le_eight (k : Fin 3)
    (κ : RationalPoints (curve k) →+ (RatSquareClassAdd × RatSquareClassAdd))
    (hκ : ∀ P, κ P=completeDescentCoordinates (curve k) 0
      (-(r2 k : ℚ)) (-(r3 k : ℚ)) P) :
    Finite κ.range ∧ Nat.card κ.range≤8 := by
  obtain ⟨hF,hcard⟩ := split_descent_image_card_le (curve k) (r2 k) (r3 k)
    (roots_nonzero_distinct k).1 (roots_nonzero_distinct k).2.1 (roots_nonzero_distinct k).2.2
    rfl (survivors k) (fullTwoSelmerTriples_subset_survivors k) κ hκ
  exact ⟨hF,by simpa only [survivors_card] using hcard⟩

end
end Z2Z4Rank6.TwistSelmer
