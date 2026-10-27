import Z2Z4Rank6.SecondExampleRankSevenSelmerData
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! Kernel certificate for the rank-seven second example. -/
namespace Z2Z4Rank6.SecondExampleRankSeven.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rowsBlock12 : ∀ k : Fin 4,
    let i : Fin 59 := ⟨48+k.val,by omega⟩
    ∀ j : Fin 61,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  decide +kernel
end Z2Z4Rank6.SecondExampleRankSeven.Selmer
