module

public import Z2Z4Rank6.TwistSelmerMatrixQ2Block00
public import Z2Z4Rank6.TwistSelmerMatrixQ2Block01
public import Z2Z4Rank6.TwistSelmerMatrixQ2Block02
public import Z2Z4Rank6.TwistSelmerMatrixQ2Block03
public import Z2Z4Rank6.TwistSelmerMatrixQ2Block04
public import Z2Z4Rank6.TwistSelmerMatrixQ2Block05
public import Z2Z4Rank6.TwistSelmerMatrixQ2Block06

@[expose] public section

/-!
# Exact reconstruction certificate for the Q2 twist
The bounded sparse checks are transported to ordinary matrix multiplication
by the proved generic evaluator equality. Source: Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.TwistSelmer

theorem q2Matrix_certificate : (1 : Matrix (Fin 55) (Fin 55) (ZMod 2))=
    q2KernelBasis*q2Projection+q2Eliminator*q2Constraints := by
  have hs : (1 : Matrix (Fin 55) (Fin 55) (ZMod 2))=
      SparseMatrixCertificate.sparseMul q2KernelBasis q2Projection+
        SparseMatrixCertificate.sparseMul q2Eliminator q2Constraints := by
    ext i j
    fin_cases i
    · exact q2Matrix_sparseCertificateBlock00 0 j
    · exact q2Matrix_sparseCertificateBlock00 1 j
    · exact q2Matrix_sparseCertificateBlock00 2 j
    · exact q2Matrix_sparseCertificateBlock00 3 j
    · exact q2Matrix_sparseCertificateBlock00 4 j
    · exact q2Matrix_sparseCertificateBlock00 5 j
    · exact q2Matrix_sparseCertificateBlock00 6 j
    · exact q2Matrix_sparseCertificateBlock00 7 j
    · exact q2Matrix_sparseCertificateBlock01 0 j
    · exact q2Matrix_sparseCertificateBlock01 1 j
    · exact q2Matrix_sparseCertificateBlock01 2 j
    · exact q2Matrix_sparseCertificateBlock01 3 j
    · exact q2Matrix_sparseCertificateBlock01 4 j
    · exact q2Matrix_sparseCertificateBlock01 5 j
    · exact q2Matrix_sparseCertificateBlock01 6 j
    · exact q2Matrix_sparseCertificateBlock01 7 j
    · exact q2Matrix_sparseCertificateBlock02 0 j
    · exact q2Matrix_sparseCertificateBlock02 1 j
    · exact q2Matrix_sparseCertificateBlock02 2 j
    · exact q2Matrix_sparseCertificateBlock02 3 j
    · exact q2Matrix_sparseCertificateBlock02 4 j
    · exact q2Matrix_sparseCertificateBlock02 5 j
    · exact q2Matrix_sparseCertificateBlock02 6 j
    · exact q2Matrix_sparseCertificateBlock02 7 j
    · exact q2Matrix_sparseCertificateBlock03 0 j
    · exact q2Matrix_sparseCertificateBlock03 1 j
    · exact q2Matrix_sparseCertificateBlock03 2 j
    · exact q2Matrix_sparseCertificateBlock03 3 j
    · exact q2Matrix_sparseCertificateBlock03 4 j
    · exact q2Matrix_sparseCertificateBlock03 5 j
    · exact q2Matrix_sparseCertificateBlock03 6 j
    · exact q2Matrix_sparseCertificateBlock03 7 j
    · exact q2Matrix_sparseCertificateBlock04 0 j
    · exact q2Matrix_sparseCertificateBlock04 1 j
    · exact q2Matrix_sparseCertificateBlock04 2 j
    · exact q2Matrix_sparseCertificateBlock04 3 j
    · exact q2Matrix_sparseCertificateBlock04 4 j
    · exact q2Matrix_sparseCertificateBlock04 5 j
    · exact q2Matrix_sparseCertificateBlock04 6 j
    · exact q2Matrix_sparseCertificateBlock04 7 j
    · exact q2Matrix_sparseCertificateBlock05 0 j
    · exact q2Matrix_sparseCertificateBlock05 1 j
    · exact q2Matrix_sparseCertificateBlock05 2 j
    · exact q2Matrix_sparseCertificateBlock05 3 j
    · exact q2Matrix_sparseCertificateBlock05 4 j
    · exact q2Matrix_sparseCertificateBlock05 5 j
    · exact q2Matrix_sparseCertificateBlock05 6 j
    · exact q2Matrix_sparseCertificateBlock05 7 j
    · exact q2Matrix_sparseCertificateBlock06 0 j
    · exact q2Matrix_sparseCertificateBlock06 1 j
    · exact q2Matrix_sparseCertificateBlock06 2 j
    · exact q2Matrix_sparseCertificateBlock06 3 j
    · exact q2Matrix_sparseCertificateBlock06 4 j
    · exact q2Matrix_sparseCertificateBlock06 5 j
    · exact q2Matrix_sparseCertificateBlock06 6 j
  simpa only [SparseMatrixCertificate.sparseMul_eq_mul] using hs

end Z2Z4Rank6.TwistSelmer
