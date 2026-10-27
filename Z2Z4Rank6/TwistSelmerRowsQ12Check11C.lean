import Z2Z4Rank6.TwistSelmerDataRowsQ12
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! One bounded semantic row check for Jaswal Proposition 5.2. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem q12Rows_row46 : ∀ j : Fin 58,
    q12Constraints 46 j=constraintEntry q12Primes (q12PrimeConstraints 46) j := by
  decide +kernel
end Z2Z4Rank6.TwistSelmer
