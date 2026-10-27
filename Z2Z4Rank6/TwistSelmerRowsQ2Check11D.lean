import Z2Z4Rank6.TwistSelmerDataRowsQ2
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! One bounded semantic row check for Jaswal Proposition 5.2. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem q2Rows_row47 : ∀ j : Fin 55,
    q2Constraints 47 j=constraintEntry q2Primes (q2PrimeConstraints 47) j := by
  decide +kernel
end Z2Z4Rank6.TwistSelmer
