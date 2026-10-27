module

public import Z2Z4Rank6.FirstExampleRankSixSelmerData
public import Z2Z4Rank6.TwistSelmerConstraintEntry

@[expose] public section

/-! Kernel certificate for the rank-six first example. -/
namespace Z2Z4Rank6.FirstExampleRankSix.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rowsBlock08 : ∀ k : Fin 4,
    let i : Fin 70 := ⟨32+k.val,by omega⟩
    ∀ j : Fin 73,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  decide +kernel
end Z2Z4Rank6.FirstExampleRankSix.Selmer
