module

public import Z2Z4Rank6.TwistSelmerDataRowsQ12
public import Z2Z4Rank6.TwistSelmerConstraintEntry

@[expose] public section

/-! One bounded semantic row check for Jaswal Proposition 5.2. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem q12Rows_row44 : ∀ j : Fin 58,
    q12Constraints 44 j=constraintEntry q12Primes (q12PrimeConstraints 44) j := by
  decide +kernel
end Z2Z4Rank6.TwistSelmer
