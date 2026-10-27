module

public import Z2Z4Rank6.TwistSelmerMatrixQ1Block00
public import Z2Z4Rank6.TwistSelmerMatrixQ1Block01
public import Z2Z4Rank6.TwistSelmerMatrixQ1Block02
public import Z2Z4Rank6.TwistSelmerMatrixQ1Block03
public import Z2Z4Rank6.TwistSelmerMatrixQ1Block04
public import Z2Z4Rank6.TwistSelmerMatrixQ1Block05
public import Z2Z4Rank6.TwistSelmerMatrixQ1Block06

@[expose] public section

/-!
# Exact reconstruction certificate for the Q1 twist
The bounded sparse checks are transported to ordinary matrix multiplication
by the proved generic evaluator equality. Source: Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.TwistSelmer

theorem q1Matrix_certificate : (1 : Matrix (Fin 49) (Fin 49) (ZMod 2))=
    q1KernelBasis*q1Projection+q1Eliminator*q1Constraints := by
  have hs : (1 : Matrix (Fin 49) (Fin 49) (ZMod 2))=
      SparseMatrixCertificate.sparseMul q1KernelBasis q1Projection+
        SparseMatrixCertificate.sparseMul q1Eliminator q1Constraints := by
    ext i j
    fin_cases i
    · exact q1Matrix_sparseCertificateBlock00 0 j
    · exact q1Matrix_sparseCertificateBlock00 1 j
    · exact q1Matrix_sparseCertificateBlock00 2 j
    · exact q1Matrix_sparseCertificateBlock00 3 j
    · exact q1Matrix_sparseCertificateBlock00 4 j
    · exact q1Matrix_sparseCertificateBlock00 5 j
    · exact q1Matrix_sparseCertificateBlock00 6 j
    · exact q1Matrix_sparseCertificateBlock00 7 j
    · exact q1Matrix_sparseCertificateBlock01 0 j
    · exact q1Matrix_sparseCertificateBlock01 1 j
    · exact q1Matrix_sparseCertificateBlock01 2 j
    · exact q1Matrix_sparseCertificateBlock01 3 j
    · exact q1Matrix_sparseCertificateBlock01 4 j
    · exact q1Matrix_sparseCertificateBlock01 5 j
    · exact q1Matrix_sparseCertificateBlock01 6 j
    · exact q1Matrix_sparseCertificateBlock01 7 j
    · exact q1Matrix_sparseCertificateBlock02 0 j
    · exact q1Matrix_sparseCertificateBlock02 1 j
    · exact q1Matrix_sparseCertificateBlock02 2 j
    · exact q1Matrix_sparseCertificateBlock02 3 j
    · exact q1Matrix_sparseCertificateBlock02 4 j
    · exact q1Matrix_sparseCertificateBlock02 5 j
    · exact q1Matrix_sparseCertificateBlock02 6 j
    · exact q1Matrix_sparseCertificateBlock02 7 j
    · exact q1Matrix_sparseCertificateBlock03 0 j
    · exact q1Matrix_sparseCertificateBlock03 1 j
    · exact q1Matrix_sparseCertificateBlock03 2 j
    · exact q1Matrix_sparseCertificateBlock03 3 j
    · exact q1Matrix_sparseCertificateBlock03 4 j
    · exact q1Matrix_sparseCertificateBlock03 5 j
    · exact q1Matrix_sparseCertificateBlock03 6 j
    · exact q1Matrix_sparseCertificateBlock03 7 j
    · exact q1Matrix_sparseCertificateBlock04 0 j
    · exact q1Matrix_sparseCertificateBlock04 1 j
    · exact q1Matrix_sparseCertificateBlock04 2 j
    · exact q1Matrix_sparseCertificateBlock04 3 j
    · exact q1Matrix_sparseCertificateBlock04 4 j
    · exact q1Matrix_sparseCertificateBlock04 5 j
    · exact q1Matrix_sparseCertificateBlock04 6 j
    · exact q1Matrix_sparseCertificateBlock04 7 j
    · exact q1Matrix_sparseCertificateBlock05 0 j
    · exact q1Matrix_sparseCertificateBlock05 1 j
    · exact q1Matrix_sparseCertificateBlock05 2 j
    · exact q1Matrix_sparseCertificateBlock05 3 j
    · exact q1Matrix_sparseCertificateBlock05 4 j
    · exact q1Matrix_sparseCertificateBlock05 5 j
    · exact q1Matrix_sparseCertificateBlock05 6 j
    · exact q1Matrix_sparseCertificateBlock05 7 j
    · exact q1Matrix_sparseCertificateBlock06 0 j
  simpa only [SparseMatrixCertificate.sparseMul_eq_mul] using hs

end Z2Z4Rank6.TwistSelmer
