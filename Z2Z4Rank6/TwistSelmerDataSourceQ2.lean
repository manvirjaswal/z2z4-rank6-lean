import Z2Z4Rank6.TwistSelmerDataLocalQ2
import Z2Z4Rank6.TwistSelmerDataFilterQ2
import Z2Z4Rank6.TwistSelmerRowsQ2
import Z2Z4Rank6.TwistSelmerMatrixQ2

/-! Canonical coverings map into the certified finite decoding pool.
Jaswal Proposition 5.2, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
open scoped BigOperators

theorem q2Source_kernel (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 1) (r3 1)) :
    q2Constraints.mulVec (bitVector q2Primes d)=0 := by
  have hs := coefficient_squarefree_of_mem d (r2 1) (r3 1) hd
  have hp (c : Fin 3) : rootProduct (r2 1) (r3 1) c∣((∏ i, q2Primes i : ℕ) : ℤ)^8 :=
    q2SupportPower c
  have hdiv := coefficient_support_bound q2Primes d (r2 1) (r3 1) 8 hp hd
  have hpos := splitCover_second_pos_of_ordered_differences d (r2 1) (r3 1)
    (roots_ordered 1).1 (roots_ordered 1).2 (hs 0).ne_zero (hs 1).ne_zero (hs 2).ne_zero
    hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
  rw [q2Rows_certificate]
  funext i
  change constraintRow q2Primes (q2PrimeConstraints i) ⬝ᵥ bitVector q2Primes d=0
  exact (constraintRow_source q2Primes q2Primes_injective q2Primes_prime d 8 hs hdiv
    hpos hd.2.2.2.2.2.2.1 (q2PrimeConstraints i)).trans (q2Constraints_satisfied d hd i)

theorem q2FullCover_mem_pool (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 1) (r3 1)) :
    d∈decodedPool q2Primes q2KernelBasis :=
  fullCover_mem_decodedPool q2Primes q2Primes_injective q2Primes_prime (r2 1) (r3 1)
    (roots_ordered 1).1 (roots_ordered 1).2 8 q2SupportPower
    q2Constraints q2KernelBasis q2Projection q2Eliminator q2Matrix_certificate
    q2Source_kernel d hd

theorem q2FullCover_mem_stageFirst (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 1) (r3 1)) : d∈q2StageFirst := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hp := q2FullCover_mem_pool d hd
  rw [q2RawPool_decode] at hp
  have ht := splitCover_local_implies_residue_test_for (p:=2) 3 d (r2 1) (r3 1)
    (hd.2.2.2.2.2.2.2.2 2)
  have hm : d∈q2RawPool.filter (splitCoverResiduePossibleFor 8 (r2 1) (r3 1)) :=
    List.mem_filter.mpr ⟨hp,ht⟩
  rwa [q2StageFirst_check] at hm

end Z2Z4Rank6.TwistSelmer
