import Z2Z4Rank6.GTwistSelmerConstraints
import Z2Z4Rank6.GTwistSelmerMatrixH
import Z2Z4Rank6.GTwistSelmerMod25
import Z2Z4Rank6.SplitDescentImage

/-!
# h-twist covering and descent-image upper certificate

Every canonical everywhere locally soluble covering of the normalized
m=-80/3 h-twist lies in sixteen explicit triples. The proof starts with the
covering, derives its matrix-kernel constraints, reconstructs its
prime factors, and applies necessary local tests modulo 8,27,25.
Source: Jaswal, Proposition 7.2(b), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.GTwistSelmer
open TwistSelmer

/-- All canonical coverings occur in the exhaustive free-bit pool. -/
theorem hFullCover_mem_pool (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : d∈decodedPool hPrimes hKernelBasis :=
  fullCover_mem_decodedPool hPrimes hPrimes_injective hPrimes_prime r2 r3
    roots_ordered.1 roots_ordered.2 8 hSupportPower
    hConstraints hKernelBasis hProjection hEliminator hMatrix_certificate
    hConstraints_mulVec_zero d hd

theorem hFullCover_mem_stageFirst (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : d∈hStageFirst := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hp := hFullCover_mem_pool d hd
  rw [hRawPool_decode] at hp
  have ht := splitCover_local_implies_residue_test_for (p:=2) 3 d r2 r3
    (hd.2.2.2.2.2.2.2.2 2)
  have hm : d∈hRawPool.filter (splitCoverResiduePossibleFor 8 r2 r3) :=
    List.mem_filter.mpr ⟨hp,ht⟩
  rwa [hStageFirst_check] at hm

theorem hFullCover_mem_stageSecond (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : d∈hStageSecond := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ht := splitCover_local_implies_residue_test_for (p:=3) 3 d r2 r3
    (hd.2.2.2.2.2.2.2.2 3)
  have hm : d∈hStageFirst.filter (splitCoverResiduePossibleFor 27 r2 r3) :=
    List.mem_filter.mpr ⟨hFullCover_mem_stageFirst d hd,ht⟩
  rwa [hStageSecond_check] at hm

theorem hFullCover_mem_stageThird (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : d∈hStageThird := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht := splitCover_local_implies_residue_test_for (p:=5) 2 d r2 r3
    (hd.2.2.2.2.2.2.2.2 5)
  have hm : d∈hStageSecond.filter (splitCoverResiduePossibleFor 25 r2 r3) :=
    List.mem_filter.mpr ⟨hFullCover_mem_stageSecond d hd,ht⟩
  rwa [hStageThird_check] at hm

/-- The canonical locally soluble covering set is contained in sixteen
explicit triples; reverse local solubility is not needed for this bound. -/
theorem fullTwoSelmerTriples_subset_survivors :
    fullTwoSelmerTriples r2 r3⊆(hStageThird.toFinset : Set ECFullTriple) := by
  intro d hd
  exact List.mem_toFinset.mpr (hFullCover_mem_stageThird d hd)

theorem hSurvivors_card : hStageThird.toFinset.card=16 := by decide +kernel

/-- The complete-descent image on the normalized rational elliptic
point group is finite and has cardinality at most sixteen. -/
theorem descent_image_card_le
    (κ : RationalPoints curve→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀ P,κ P=completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P) :
    Finite κ.range∧Nat.card κ.range≤16 := by
  have h := split_descent_image_card_le curve r2 r3
    roots_nonzero_distinct.1 roots_nonzero_distinct.2.1 roots_nonzero_distinct.2.2
    rfl hStageThird.toFinset fullTwoSelmerTriples_subset_survivors κ hκ
  simpa only [hSurvivors_card] using h

end Z2Z4Rank6.GTwistSelmer
