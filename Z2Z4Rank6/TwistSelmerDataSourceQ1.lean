module

public import Z2Z4Rank6.TwistSelmerDataLocalQ1
public import Z2Z4Rank6.TwistSelmerDataFilterQ1
public import Z2Z4Rank6.TwistSelmerRowsQ1
public import Z2Z4Rank6.TwistSelmerMatrixQ1

@[expose] public section

/-! Canonical coverings map into the certified finite decoding pool.
Jaswal Proposition 5.2, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
open scoped BigOperators

theorem q1Source_kernel (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 0) (r3 0)) :
    q1Constraints.mulVec (bitVector q1Primes d)=0 := by
  have hs := coefficient_squarefree_of_mem d (r2 0) (r3 0) hd
  have hp (c : Fin 3) : rootProduct (r2 0) (r3 0) c∣((∏ i, q1Primes i : ℕ) : ℤ)^8 :=
    q1SupportPower c
  have hdiv := coefficient_support_bound q1Primes d (r2 0) (r3 0) 8 hp hd
  have hpos := splitCover_second_pos_of_ordered_differences d (r2 0) (r3 0)
    (roots_ordered 0).1 (roots_ordered 0).2 (hs 0).ne_zero (hs 1).ne_zero (hs 2).ne_zero
    hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
  rw [q1Rows_certificate]
  funext i
  change constraintRow q1Primes (q1PrimeConstraints i) ⬝ᵥ bitVector q1Primes d=0
  exact (constraintRow_source q1Primes q1Primes_injective q1Primes_prime d 8 hs hdiv
    hpos hd.2.2.2.2.2.2.1 (q1PrimeConstraints i)).trans (q1Constraints_satisfied d hd i)

theorem q1FullCover_mem_pool (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 0) (r3 0)) :
    d∈decodedPool q1Primes q1KernelBasis :=
  fullCover_mem_decodedPool q1Primes q1Primes_injective q1Primes_prime (r2 0) (r3 0)
    (roots_ordered 0).1 (roots_ordered 0).2 8 q1SupportPower
    q1Constraints q1KernelBasis q1Projection q1Eliminator q1Matrix_certificate
    q1Source_kernel d hd

theorem q1FullCover_mem_stageFirst (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 0) (r3 0)) : d∈q1StageFirst := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hp := q1FullCover_mem_pool d hd
  rw [q1RawPool_decode] at hp
  have ht := splitCover_local_implies_residue_test_for (p:=2) 4 d (r2 0) (r3 0)
    (hd.2.2.2.2.2.2.2.2 2)
  have hm : d∈q1RawPool.filter (splitCoverResiduePossibleFor 16 (r2 0) (r3 0)) :=
    List.mem_filter.mpr ⟨hp,ht⟩
  rwa [q1StageFirst_check] at hm

end Z2Z4Rank6.TwistSelmer
