import Z2Z4Rank6.TwistSelmerDataRowsQ12
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! A kernel check of the semantic rows in Jaswal Proposition 5.2,
DOI: 10.5281/zenodo.23437117. The block has at most four rows. -/

namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem q12Rows_block05 : ∀ k : Fin 4,
    let i : Fin 52 := ⟨20+k.val,by omega⟩
    ∀ j : Fin 58, q12Constraints i j=constraintEntry q12Primes (q12PrimeConstraints i) j := by
  decide +kernel
end Z2Z4Rank6.TwistSelmer
