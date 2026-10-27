module

public import Z2Z4Rank6.TwistSelmerRowsQ12Check11A
public import Z2Z4Rank6.TwistSelmerRowsQ12Check11B
public import Z2Z4Rank6.TwistSelmerRowsQ12Check11C
public import Z2Z4Rank6.TwistSelmerRowsQ12Check11D

@[expose] public section

/-! Assembly of four kernel-checked semantic rows. -/
namespace Z2Z4Rank6.TwistSelmer
theorem q12Rows_block11 : ∀ k : Fin 4,
    let i : Fin 52 := ⟨44+k.val,by omega⟩
    ∀ j : Fin 58, q12Constraints i j=constraintEntry q12Primes (q12PrimeConstraints i) j := by
  intro k
  fin_cases k
  · exact q12Rows_row44
  · exact q12Rows_row45
  · exact q12Rows_row46
  · exact q12Rows_row47
end Z2Z4Rank6.TwistSelmer
