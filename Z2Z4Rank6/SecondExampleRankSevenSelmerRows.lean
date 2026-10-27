module

public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock00
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock01
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock02
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock03
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock04
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock05
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock06
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock07
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock08
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock09
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock10
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock11
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock12
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock13
public import Z2Z4Rank6.SecondExampleRankSevenSelmerRowsBlock14

@[expose] public section

namespace Z2Z4Rank6.SecondExampleRankSeven.Selmer
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
  · exact rowsBlock12 1 j
  · exact rowsBlock12 2 j
  · exact rowsBlock12 3 j
  · exact rowsBlock13 0 j
  · exact rowsBlock13 1 j
  · exact rowsBlock13 2 j
  · exact rowsBlock13 3 j
  · exact rowsBlock14 0 j
  · exact rowsBlock14 1 j
  · exact rowsBlock14 2 j
end Z2Z4Rank6.SecondExampleRankSeven.Selmer
