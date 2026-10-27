import Z2Z4Rank6.GExampleRankSixSelmerData
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! Kernel certificate for the rank-six G-fiber example. -/
namespace Z2Z4Rank6.GExampleRankSix.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rowsBlock12 : ∀ k : Fin 4,
    let i : Fin 52 := ⟨48+k.val,by omega⟩
    ∀ j : Fin 55,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  decide +kernel
end Z2Z4Rank6.GExampleRankSix.Selmer
