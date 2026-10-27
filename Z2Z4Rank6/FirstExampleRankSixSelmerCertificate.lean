import Z2Z4Rank6.FirstExampleRankSixSelmerRows
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrix
import Z2Z4Rank6.FirstExampleRankSixSelmerLocal
import Z2Z4Rank6.FirstExampleRankSixSelmerCounting
import Z2Z4Rank6.SplitDescentImage

/-!
# 256-class upper certificate for the first rank-six example

Every canonical everywhere locally soluble covering satisfies the
twenty-two proved local character conditions and the support/product rows.
The exact matrix identity reconstructs its coefficients from eight
free bits, bounding the complete-descent image by 256.
Source: Jaswal, before Proposition 6.2, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.FirstExampleRankSix.Selmer
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators

/-- Covering membership implies the certified finite matrix kernel. -/
theorem source_kernel (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    constraints.mulVec (bitVector primes d)=0 := by
  have hs := coefficient_squarefree_of_mem d r2 r3 hd
  have hdiv := coefficient_support_bound primes d r2 r3 20 supportPower hd
  have hpos := splitCover_second_pos_of_ordered_differences d r2 r3
    roots_ordered.1 roots_ordered.2 (hs 0).ne_zero (hs 1).ne_zero (hs 2).ne_zero
    hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
  rw [rows_certificate]
  funext i
  change constraintRow primes (primeConstraints i) ⬝ᵥ bitVector primes d=0
  exact (constraintRow_source primes primes_injective primes_prime d 20 hs hdiv
    hpos hd.2.2.2.2.2.2.1 (primeConstraints i)).trans (constraints_satisfied d hd i)

theorem fullCover_mem_pool (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    d∈finiteKernelPool primes kernelBasis :=
  mem_finiteKernelPool primes kernelBasis d
    (fullCover_mem_decodedPool primes primes_injective primes_prime r2 r3
      roots_ordered.1 roots_ordered.2 20 supportPower constraints kernelBasis
      projectionMatrix eliminator matrix_certificate source_kernel d hd)

theorem fullTwoSelmerTriples_subset_pool :
    fullTwoSelmerTriples r2 r3⊆(finiteKernelPool primes kernelBasis : Set ECFullTriple) :=
  fun _ hd => fullCover_mem_pool _ hd

/-- Cardinality bound on the canonical locally soluble covering set. -/
theorem fullTwoSelmerTriples_card_le :
    (fullTwoSelmerTriples r2 r3).Finite ∧ (fullTwoSelmerTriples r2 r3).ncard≤256 := by
  have hfin := (finiteKernelPool primes kernelBasis).finite_toSet
  refine ⟨hfin.subset fullTwoSelmerTriples_subset_pool,?_⟩
  calc
    _ ≤ (finiteKernelPool primes kernelBasis : Set ECFullTriple).ncard :=
      Set.ncard_le_ncard fullTwoSelmerTriples_subset_pool hfin
    _ = (finiteKernelPool primes kernelBasis).card := Set.ncard_coe_finset _
    _ ≤ 256 := by simpa using finiteKernelPool_card_le primes kernelBasis

theorem roots_nonzero_distinct : r2≠0 ∧ r3≠0 ∧ r2≠r3 := by norm_num [r2,r3]

theorem curve_split : curve=splitWeierstrass 0 (-(r2:ℚ)) (-(r3:ℚ)) := by
  ext <;> norm_num [curve,E,A,B,splitWeierstrass,r2,r3]

/-- The complete-descent image has at most 256 classes. -/
theorem descent_image_card_le
    (κ : RationalPoints curve→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates curve 0 (-(r2:ℚ)) (-(r3:ℚ)) P) :
    Finite κ.range ∧ Nat.card κ.range≤256 := by
  obtain ⟨hfin,hcard⟩ := split_descent_image_card_le curve r2 r3
    roots_nonzero_distinct.1 roots_nonzero_distinct.2.1 roots_nonzero_distinct.2.2
    curve_split (finiteKernelPool primes kernelBasis) fullTwoSelmerTriples_subset_pool κ hκ
  exact ⟨hfin,hcard.trans (by simpa using finiteKernelPool_card_le primes kernelBasis)⟩

end Z2Z4Rank6.FirstExampleRankSix.Selmer
