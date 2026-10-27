import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock00
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock01
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock02
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock03
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock04
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock05
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock06
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock07
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock08
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock09
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock10
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock11
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock12
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock13
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock14
import Z2Z4Rank6.ConicRankNineCertificateSelmerRowsBlock15

namespace Z2Z4Rank6.ConicRankNineCertificate.Selmer
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
  · exact rowsBlock14 3 j
  · exact rowsBlock15 0 j
  · exact rowsBlock15 1 j
  · exact rowsBlock15 2 j
  · exact rowsBlock15 3 j
end Z2Z4Rank6.ConicRankNineCertificate.Selmer
