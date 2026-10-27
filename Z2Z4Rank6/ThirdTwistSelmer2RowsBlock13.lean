import Z2Z4Rank6.ThirdTwistSelmer2Data
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer2
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem rowsBlock13 : ∀ k : Fin 1,
    let i : Fin 53 := ⟨52+k.val,by omega⟩
    ∀ j : Fin 55,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  decide +kernel

end Z2Z4Rank6.ThirdTwist.Selmer2
