module

public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock00
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock01
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock02
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock03
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock04
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock05
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock06
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock07
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock08
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock09
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock10
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock11
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock12
public import Z2Z4Rank6.ThirdTwistSelmer1MatrixBlock13

@[expose] public section

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer1
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
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

end Z2Z4Rank6.ThirdTwist.Selmer1
