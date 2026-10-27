import Z2Z4Rank6.TwistSelmerRowsQ2Check11A
import Z2Z4Rank6.TwistSelmerRowsQ2Check11B
import Z2Z4Rank6.TwistSelmerRowsQ2Check11C
import Z2Z4Rank6.TwistSelmerRowsQ2Check11D

/-! Assembly of four kernel-checked semantic rows. -/
namespace Z2Z4Rank6.TwistSelmer
theorem q2Rows_block11 : ∀ k : Fin 4,
    let i : Fin 51 := ⟨44+k.val,by omega⟩
    ∀ j : Fin 55, q2Constraints i j=constraintEntry q2Primes (q2PrimeConstraints i) j := by
  intro k
  fin_cases k
  · exact q2Rows_row44
  · exact q2Rows_row45
  · exact q2Rows_row46
  · exact q2Rows_row47
end Z2Z4Rank6.TwistSelmer
