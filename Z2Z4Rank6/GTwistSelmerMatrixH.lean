module

public import Z2Z4Rank6.GTwistSelmerMatrixHBlock00
public import Z2Z4Rank6.GTwistSelmerMatrixHBlock01
public import Z2Z4Rank6.GTwistSelmerMatrixHBlock02
public import Z2Z4Rank6.GTwistSelmerMatrixHBlock03
public import Z2Z4Rank6.GTwistSelmerMatrixHBlock04
public import Z2Z4Rank6.GTwistSelmerMatrixHBlock05
public import Z2Z4Rank6.GTwistSelmerMatrixHBlock06

@[expose] public section

/-! Exact reconstruction identity for the h-twist matrix. -/
namespace Z2Z4Rank6.GTwistSelmer

theorem hMatrix_certificate :
    (1 : Matrix (Fin 55) (Fin 55) (ZMod 2))=
      hKernelBasis*hProjection+hEliminator*hConstraints := by
  ext i j
  rw [←SparseMatrixCertificate.sparseMul_eq_mul hKernelBasis hProjection,
    ←SparseMatrixCertificate.sparseMul_eq_mul hEliminator hConstraints]
  fin_cases i
  · exact hMatrix_sparseCertificateBlock00 ⟨0,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock00 ⟨1,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock00 ⟨2,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock00 ⟨3,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock00 ⟨4,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock00 ⟨5,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock00 ⟨6,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock00 ⟨7,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨0,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨1,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨2,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨3,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨4,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨5,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨6,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock01 ⟨7,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨0,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨1,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨2,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨3,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨4,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨5,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨6,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock02 ⟨7,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨0,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨1,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨2,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨3,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨4,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨5,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨6,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock03 ⟨7,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨0,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨1,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨2,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨3,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨4,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨5,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨6,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock04 ⟨7,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨0,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨1,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨2,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨3,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨4,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨5,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨6,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock05 ⟨7,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock06 ⟨0,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock06 ⟨1,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock06 ⟨2,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock06 ⟨3,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock06 ⟨4,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock06 ⟨5,by decide⟩ j
  · exact hMatrix_sparseCertificateBlock06 ⟨6,by decide⟩ j

end Z2Z4Rank6.GTwistSelmer
