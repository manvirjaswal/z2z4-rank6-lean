module

public import Z2Z4Rank6.TwistSelmerDataLocalQ12
public import Z2Z4Rank6.TwistSelmerDataFilterQ12
public import Z2Z4Rank6.TwistSelmerRowsQ12
public import Z2Z4Rank6.TwistSelmerMatrixQ12

@[expose] public section

/-! Canonical coverings map into the certified finite decoding pool.
Jaswal Proposition 5.2, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
open scoped BigOperators

theorem q12Source_kernel (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 2) (r3 2)) :
    q12Constraints.mulVec (bitVector q12Primes d)=0 := by
  have hs := coefficient_squarefree_of_mem d (r2 2) (r3 2) hd
  have hp (c : Fin 3) : rootProduct (r2 2) (r3 2) c∣((∏ i, q12Primes i : ℕ) : ℤ)^8 :=
    q12SupportPower c
  have hdiv := coefficient_support_bound q12Primes d (r2 2) (r3 2) 8 hp hd
  have hpos := splitCover_second_pos_of_ordered_differences d (r2 2) (r3 2)
    (roots_ordered 2).1 (roots_ordered 2).2 (hs 0).ne_zero (hs 1).ne_zero (hs 2).ne_zero
    hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
  rw [q12Rows_certificate]
  funext i
  change constraintRow q12Primes (q12PrimeConstraints i) ⬝ᵥ bitVector q12Primes d=0
  exact (constraintRow_source q12Primes q12Primes_injective q12Primes_prime d 8 hs hdiv
    hpos hd.2.2.2.2.2.2.1 (q12PrimeConstraints i)).trans (q12Constraints_satisfied d hd i)

theorem q12FullCover_mem_pool (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 2) (r3 2)) :
    d∈decodedPool q12Primes q12KernelBasis :=
  fullCover_mem_decodedPool q12Primes q12Primes_injective q12Primes_prime (r2 2) (r3 2)
    (roots_ordered 2).1 (roots_ordered 2).2 8 q12SupportPower
    q12Constraints q12KernelBasis q12Projection q12Eliminator q12Matrix_certificate
    q12Source_kernel d hd

theorem q12FullCover_mem_stageFirst (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 2) (r3 2)) : d∈q12StageFirst := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hp := q12FullCover_mem_pool d hd
  rw [q12RawPool_decode] at hp
  have ht := splitCover_local_implies_residue_test_for (p:=2) 4 d (r2 2) (r3 2)
    (hd.2.2.2.2.2.2.2.2 2)
  have hm : d∈q12RawPool.filter (splitCoverResiduePossibleFor 16 (r2 2) (r3 2)) :=
    List.mem_filter.mpr ⟨hp,ht⟩
  rwa [q12StageFirst_check] at hm

end Z2Z4Rank6.TwistSelmer
