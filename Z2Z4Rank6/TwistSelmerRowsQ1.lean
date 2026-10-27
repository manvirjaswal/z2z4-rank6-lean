import Z2Z4Rank6.TwistSelmerRowsQ1Check00
import Z2Z4Rank6.TwistSelmerRowsQ1Check01
import Z2Z4Rank6.TwistSelmerRowsQ1Check02
import Z2Z4Rank6.TwistSelmerRowsQ1Check03
import Z2Z4Rank6.TwistSelmerRowsQ1Check04
import Z2Z4Rank6.TwistSelmerRowsQ1Check05
import Z2Z4Rank6.TwistSelmerRowsQ1Check06
import Z2Z4Rank6.TwistSelmerRowsQ1Check07
import Z2Z4Rank6.TwistSelmerRowsQ1Check08
import Z2Z4Rank6.TwistSelmerRowsQ1Check09
import Z2Z4Rank6.TwistSelmerRowsQ1Check10

/-! # Exact semantic rows for the q1-twist certificate

Each matrix row is identified with the covering constraint it encodes.
Source: Jaswal Proposition 5.2, DOI: 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TwistSelmer

theorem q1Rows_certificate :
    q1Constraints = fun i => constraintRow q1Primes (q1PrimeConstraints i) := by
  funext i j
  rw [constraintRow_eq_constraintEntry]
  fin_cases i
  · exact q1Rows_block00 0 j
  · exact q1Rows_block00 1 j
  · exact q1Rows_block00 2 j
  · exact q1Rows_block00 3 j
  · exact q1Rows_block01 0 j
  · exact q1Rows_block01 1 j
  · exact q1Rows_block01 2 j
  · exact q1Rows_block01 3 j
  · exact q1Rows_block02 0 j
  · exact q1Rows_block02 1 j
  · exact q1Rows_block02 2 j
  · exact q1Rows_block02 3 j
  · exact q1Rows_block03 0 j
  · exact q1Rows_block03 1 j
  · exact q1Rows_block03 2 j
  · exact q1Rows_block03 3 j
  · exact q1Rows_block04 0 j
  · exact q1Rows_block04 1 j
  · exact q1Rows_block04 2 j
  · exact q1Rows_block04 3 j
  · exact q1Rows_block05 0 j
  · exact q1Rows_block05 1 j
  · exact q1Rows_block05 2 j
  · exact q1Rows_block05 3 j
  · exact q1Rows_block06 0 j
  · exact q1Rows_block06 1 j
  · exact q1Rows_block06 2 j
  · exact q1Rows_block06 3 j
  · exact q1Rows_block07 0 j
  · exact q1Rows_block07 1 j
  · exact q1Rows_block07 2 j
  · exact q1Rows_block07 3 j
  · exact q1Rows_block08 0 j
  · exact q1Rows_block08 1 j
  · exact q1Rows_block08 2 j
  · exact q1Rows_block08 3 j
  · exact q1Rows_block09 0 j
  · exact q1Rows_block09 1 j
  · exact q1Rows_block09 2 j
  · exact q1Rows_block09 3 j
  · exact q1Rows_block10 0 j
  · exact q1Rows_block10 1 j

end Z2Z4Rank6.TwistSelmer
