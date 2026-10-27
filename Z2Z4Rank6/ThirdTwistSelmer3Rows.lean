import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock00
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock01
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock02
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock03
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock04
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock05
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock06
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock07
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock08
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock09
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock10
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock11
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock12
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock13
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock14
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock15
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock16
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock17
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock18
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock19
import Z2Z4Rank6.ThirdTwistSelmer3RowsBlock20

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem rows_certificate : constraints=fun i => TwistSelmer.constraintRow primes (primeConstraints i) := by
  funext i j
  rw [TwistSelmer.constraintRow_eq_constraintEntry]
  fin_cases i
  · exact rowsBlock00 0 j
  · exact rowsBlock00 1 j
  · exact rowsBlock00 2 j
  · exact rowsBlock00 3 j
  · exact rowsBlock01 0 j
  · exact rowsBlock01 1 j
  · exact rowsBlock01 2 j
  · exact rowsBlock01 3 j
  · exact rowsBlock02 0 j
  · exact rowsBlock02 1 j
  · exact rowsBlock02 2 j
  · exact rowsBlock02 3 j
  · exact rowsBlock03 0 j
  · exact rowsBlock03 1 j
  · exact rowsBlock03 2 j
  · exact rowsBlock03 3 j
  · exact rowsBlock04 0 j
  · exact rowsBlock04 1 j
  · exact rowsBlock04 2 j
  · exact rowsBlock04 3 j
  · exact rowsBlock05 0 j
  · exact rowsBlock05 1 j
  · exact rowsBlock05 2 j
  · exact rowsBlock05 3 j
  · exact rowsBlock06 0 j
  · exact rowsBlock06 1 j
  · exact rowsBlock06 2 j
  · exact rowsBlock06 3 j
  · exact rowsBlock07 0 j
  · exact rowsBlock07 1 j
  · exact rowsBlock07 2 j
  · exact rowsBlock07 3 j
  · exact rowsBlock08 0 j
  · exact rowsBlock08 1 j
  · exact rowsBlock08 2 j
  · exact rowsBlock08 3 j
  · exact rowsBlock09 0 j
  · exact rowsBlock09 1 j
  · exact rowsBlock09 2 j
  · exact rowsBlock09 3 j
  · exact rowsBlock10 0 j
  · exact rowsBlock10 1 j
  · exact rowsBlock10 2 j
  · exact rowsBlock10 3 j
  · exact rowsBlock11 0 j
  · exact rowsBlock11 1 j
  · exact rowsBlock11 2 j
  · exact rowsBlock11 3 j
  · exact rowsBlock12 0 j
  · exact rowsBlock13 0 j
  · exact rowsBlock14 0 j
  · exact rowsBlock15 0 j
  · exact rowsBlock16 0 j
  · exact rowsBlock17 0 j
  · exact rowsBlock18 0 j
  · exact rowsBlock19 0 j
  · exact rowsBlock20 0 j

end Z2Z4Rank6.ThirdTwist.Selmer3
