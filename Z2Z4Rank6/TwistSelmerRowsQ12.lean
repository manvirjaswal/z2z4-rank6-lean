module

public import Z2Z4Rank6.TwistSelmerRowsQ12Check00
public import Z2Z4Rank6.TwistSelmerRowsQ12Check01
public import Z2Z4Rank6.TwistSelmerRowsQ12Check02
public import Z2Z4Rank6.TwistSelmerRowsQ12Check03
public import Z2Z4Rank6.TwistSelmerRowsQ12Check04
public import Z2Z4Rank6.TwistSelmerRowsQ12Check05
public import Z2Z4Rank6.TwistSelmerRowsQ12Check06
public import Z2Z4Rank6.TwistSelmerRowsQ12Check07
public import Z2Z4Rank6.TwistSelmerRowsQ12Check08
public import Z2Z4Rank6.TwistSelmerRowsQ12Check09
public import Z2Z4Rank6.TwistSelmerRowsQ12Check10
public import Z2Z4Rank6.TwistSelmerRowsQ12Check11
public import Z2Z4Rank6.TwistSelmerRowsQ12Check12

@[expose] public section

/-! # Exact semantic rows for the q12-twist certificate

Each matrix row is identified with the covering constraint it encodes.
Source: Jaswal Proposition 5.2, DOI: 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TwistSelmer

theorem q12Rows_certificate :
    q12Constraints = fun i => constraintRow q12Primes (q12PrimeConstraints i) := by
  funext i j
  rw [constraintRow_eq_constraintEntry]
  fin_cases i
  · exact q12Rows_block00 0 j
  · exact q12Rows_block00 1 j
  · exact q12Rows_block00 2 j
  · exact q12Rows_block00 3 j
  · exact q12Rows_block01 0 j
  · exact q12Rows_block01 1 j
  · exact q12Rows_block01 2 j
  · exact q12Rows_block01 3 j
  · exact q12Rows_block02 0 j
  · exact q12Rows_block02 1 j
  · exact q12Rows_block02 2 j
  · exact q12Rows_block02 3 j
  · exact q12Rows_block03 0 j
  · exact q12Rows_block03 1 j
  · exact q12Rows_block03 2 j
  · exact q12Rows_block03 3 j
  · exact q12Rows_block04 0 j
  · exact q12Rows_block04 1 j
  · exact q12Rows_block04 2 j
  · exact q12Rows_block04 3 j
  · exact q12Rows_block05 0 j
  · exact q12Rows_block05 1 j
  · exact q12Rows_block05 2 j
  · exact q12Rows_block05 3 j
  · exact q12Rows_block06 0 j
  · exact q12Rows_block06 1 j
  · exact q12Rows_block06 2 j
  · exact q12Rows_block06 3 j
  · exact q12Rows_block07 0 j
  · exact q12Rows_block07 1 j
  · exact q12Rows_block07 2 j
  · exact q12Rows_block07 3 j
  · exact q12Rows_block08 0 j
  · exact q12Rows_block08 1 j
  · exact q12Rows_block08 2 j
  · exact q12Rows_block08 3 j
  · exact q12Rows_block09 0 j
  · exact q12Rows_block09 1 j
  · exact q12Rows_block09 2 j
  · exact q12Rows_block09 3 j
  · exact q12Rows_block10 0 j
  · exact q12Rows_block10 1 j
  · exact q12Rows_block10 2 j
  · exact q12Rows_block10 3 j
  · exact q12Rows_block11 0 j
  · exact q12Rows_block11 1 j
  · exact q12Rows_block11 2 j
  · exact q12Rows_block11 3 j
  · exact q12Rows_block12 0 j
  · exact q12Rows_block12 1 j
  · exact q12Rows_block12 2 j
  · exact q12Rows_block12 3 j

end Z2Z4Rank6.TwistSelmer
