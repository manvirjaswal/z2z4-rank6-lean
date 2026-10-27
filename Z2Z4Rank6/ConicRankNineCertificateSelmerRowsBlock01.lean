import Z2Z4Rank6.ConicRankNineCertificateSelmerData
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! Kernel certificate for the rank-nine conic fiber. -/
namespace Z2Z4Rank6.ConicRankNineCertificate.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rowsBlock01 : ∀ k : Fin 4,
    let i : Fin 64 := ⟨4+k.val,by omega⟩
    ∀ j : Fin 67,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  decide +kernel
end Z2Z4Rank6.ConicRankNineCertificate.Selmer
