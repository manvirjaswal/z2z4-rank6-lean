import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock00
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock01
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock02
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock03
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock04
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock05
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock06
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock07
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock08
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock09
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock10
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock11
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock12
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock13
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock14
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock15
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock16
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock17
import Z2Z4Rank6.FirstExampleRankSixSelmerMatrixBlock18

namespace Z2Z4Rank6.FirstExampleRankSix.Selmer
theorem matrix_certificate : (1 : Matrix (Fin 73) (Fin 73) (ZMod 2))=
    kernelBasis*projectionMatrix+eliminator*constraints := by
  ext i j
  rw [←SparseMatrixCertificate.sparseMul_eq_mul kernelBasis projectionMatrix,
    ←SparseMatrixCertificate.sparseMul_eq_mul eliminator constraints]
  fin_cases i
  · exact matrixBlock00 0 j
  · exact matrixBlock00 1 j
  · exact matrixBlock00 2 j
  · exact matrixBlock00 3 j
  · exact matrixBlock01 0 j
  · exact matrixBlock01 1 j
  · exact matrixBlock01 2 j
  · exact matrixBlock01 3 j
  · exact matrixBlock02 0 j
  · exact matrixBlock02 1 j
  · exact matrixBlock02 2 j
  · exact matrixBlock02 3 j
  · exact matrixBlock03 0 j
  · exact matrixBlock03 1 j
  · exact matrixBlock03 2 j
  · exact matrixBlock03 3 j
  · exact matrixBlock04 0 j
  · exact matrixBlock04 1 j
  · exact matrixBlock04 2 j
  · exact matrixBlock04 3 j
  · exact matrixBlock05 0 j
  · exact matrixBlock05 1 j
  · exact matrixBlock05 2 j
  · exact matrixBlock05 3 j
  · exact matrixBlock06 0 j
  · exact matrixBlock06 1 j
  · exact matrixBlock06 2 j
  · exact matrixBlock06 3 j
  · exact matrixBlock07 0 j
  · exact matrixBlock07 1 j
  · exact matrixBlock07 2 j
  · exact matrixBlock07 3 j
  · exact matrixBlock08 0 j
  · exact matrixBlock08 1 j
  · exact matrixBlock08 2 j
  · exact matrixBlock08 3 j
  · exact matrixBlock09 0 j
  · exact matrixBlock09 1 j
  · exact matrixBlock09 2 j
  · exact matrixBlock09 3 j
  · exact matrixBlock10 0 j
  · exact matrixBlock10 1 j
  · exact matrixBlock10 2 j
  · exact matrixBlock10 3 j
  · exact matrixBlock11 0 j
  · exact matrixBlock11 1 j
  · exact matrixBlock11 2 j
  · exact matrixBlock11 3 j
  · exact matrixBlock12 0 j
  · exact matrixBlock12 1 j
  · exact matrixBlock12 2 j
  · exact matrixBlock12 3 j
  · exact matrixBlock13 0 j
  · exact matrixBlock13 1 j
  · exact matrixBlock13 2 j
  · exact matrixBlock13 3 j
  · exact matrixBlock14 0 j
  · exact matrixBlock14 1 j
  · exact matrixBlock14 2 j
  · exact matrixBlock14 3 j
  · exact matrixBlock15 0 j
  · exact matrixBlock15 1 j
  · exact matrixBlock15 2 j
  · exact matrixBlock15 3 j
  · exact matrixBlock16 0 j
  · exact matrixBlock16 1 j
  · exact matrixBlock16 2 j
  · exact matrixBlock16 3 j
  · exact matrixBlock17 0 j
  · exact matrixBlock17 1 j
  · exact matrixBlock17 2 j
  · exact matrixBlock17 3 j
  · exact matrixBlock18 0 j
end Z2Z4Rank6.FirstExampleRankSix.Selmer
