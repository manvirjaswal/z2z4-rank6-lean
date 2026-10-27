import Z2Z4Rank6.ThirdTwistSelmer0Rows
import Z2Z4Rank6.ThirdTwistSelmer0Matrix
import Z2Z4Rank6.ThirdTwistSelmer0Local
import Z2Z4Rank6.ThirdTwistSelmer0Mod25
import Z2Z4Rank6.SplitDescentImage

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer0
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem source_kernel (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    constraints.mulVec (bitVector primes d)=0 := by
  have hs := coefficient_squarefree_of_mem d r2 r3 hd
  have hdiv := coefficient_support_bound primes d r2 r3 10 supportPower hd
  have hpos := splitCover_second_pos_of_ordered_differences d r2 r3
    roots_ordered.1 roots_ordered.2 (hs 0).ne_zero (hs 1).ne_zero (hs 2).ne_zero
    hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
  rw [rows_certificate]
  funext i
  exact (constraintRow_source primes primes_injective primes_prime d 10 hs hdiv
    hpos hd.2.2.2.2.2.2.1 (primeConstraints i)).trans (constraints_satisfied d hd i)
theorem fullCover_mem_pool (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) : d∈rawPool := by
  rw [←rawPool_decode]
  exact fullCover_mem_decodedPool primes primes_injective primes_prime r2 r3
    roots_ordered.1 roots_ordered.2 10 supportPower constraints kernelBasis
    projectionMatrix eliminator matrix_certificate source_kernel d hd
theorem fullCover_mem_stage0 (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : d∈stage0 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have ht := splitCover_local_implies_residue_test_for (p:=2) 4 d r2 r3
    (hd.2.2.2.2.2.2.2.2 2)
  have hm : d∈rawPool.filter (splitCoverResiduePossibleFor 16 r2 r3) :=
    List.mem_filter.mpr ⟨fullCover_mem_pool d hd,ht⟩
  rwa [stage0_check] at hm
theorem fullCover_mem_stage1 (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : d∈stage1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ht := splitCover_local_implies_residue_test_for (p:=3) 3 d r2 r3
    (hd.2.2.2.2.2.2.2.2 3)
  have hm : d∈stage0.filter (splitCoverResiduePossibleFor 27 r2 r3) :=
    List.mem_filter.mpr ⟨fullCover_mem_stage0 d hd,ht⟩
  rwa [stage1_check] at hm
theorem fullCover_mem_stage2 (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples r2 r3) : d∈stage2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht := splitCover_local_implies_residue_test_for (p:=5) 2 d r2 r3
    (hd.2.2.2.2.2.2.2.2 5)
  have hm : d∈stage1.filter (splitCoverResiduePossibleFor 25 r2 r3) :=
    List.mem_filter.mpr ⟨fullCover_mem_stage1 d hd,ht⟩
  rwa [stage2_check] at hm
def survivors : Finset ECFullTriple := stage2.toFinset
theorem fullTwoSelmerTriples_subset_survivors :
    fullTwoSelmerTriples r2 r3⊆(survivors : Set ECFullTriple) := by
  intro d hd
  exact List.mem_toFinset.mpr (fullCover_mem_stage2 d hd)
theorem survivors_card : survivors.card=8 := by decide +kernel
theorem descent_image_card_le
    (κ : RationalPoints (ThirdTwist.curve 0)→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates (ThirdTwist.curve 0) 0 (-(r2:ℚ)) (-(r3:ℚ)) P) :
    Finite κ.range ∧ Nat.card κ.range≤8 := by
  have h := split_descent_image_card_le (ThirdTwist.curve 0) r2 r3
    roots_nonzero_distinct.1 roots_nonzero_distinct.2.1 roots_nonzero_distinct.2.2
    rfl survivors fullTwoSelmerTriples_subset_survivors κ hκ
  simpa only [survivors_card] using h

end Z2Z4Rank6.ThirdTwist.Selmer0
