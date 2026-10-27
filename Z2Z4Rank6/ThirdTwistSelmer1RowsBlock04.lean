module

public import Z2Z4Rank6.ThirdTwistSelmer1Data
public import Z2Z4Rank6.TwistSelmerConstraintEntry

@[expose] public section

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer1
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem rowsBlock04 : ∀ k : Fin 4,
    let i : Fin 50 := ⟨16+k.val,by omega⟩
    ∀ j : Fin 55,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  decide +kernel

end Z2Z4Rank6.ThirdTwist.Selmer1
