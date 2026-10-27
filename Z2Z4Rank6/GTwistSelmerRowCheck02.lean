module

public import Z2Z4Rank6.GTwistSelmerRows
public import Z2Z4Rank6.TwistSelmerConstraintEntry

@[expose] public section

/-! A bounded exact matrix-to-semantic-row comparison. -/
namespace Z2Z4Rank6.GTwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem hRowCheck02 : ∀ k : Fin 8,
    let i : Fin 50 := ⟨16+k.val,by omega⟩
    ∀ j : Fin 55, hConstraints i j=TwistSelmer.constraintEntry hPrimes (hPrimeConstraints i) j := by
  decide +kernel
end Z2Z4Rank6.GTwistSelmer
