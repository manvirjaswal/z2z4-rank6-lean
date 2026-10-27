module

public import Z2Z4Rank6.GExampleRankSixSelmerData
public import Z2Z4Rank6.TwistSelmerConstraintEntry

@[expose] public section

/-! Kernel certificate for the rank-six G-fiber example. -/
namespace Z2Z4Rank6.GExampleRankSix.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rowsBlock11 : ∀ k : Fin 4,
    let i : Fin 52 := ⟨44+k.val,by omega⟩
    ∀ j : Fin 55,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  decide +kernel
end Z2Z4Rank6.GExampleRankSix.Selmer
