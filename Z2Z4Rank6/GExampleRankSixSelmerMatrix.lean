import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock00
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock01
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock02
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock03
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock04
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock05
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock06
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock07
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock08
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock09
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock10
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock11
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock12
import Z2Z4Rank6.GExampleRankSixSelmerMatrixBlock13

namespace Z2Z4Rank6.GExampleRankSix.Selmer
theorem matrix_certificate : (1 : Matrix (Fin 55) (Fin 55) (ZMod 2))=
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
end Z2Z4Rank6.GExampleRankSix.Selmer
