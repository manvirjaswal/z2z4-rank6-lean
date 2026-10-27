import Z2Z4Rank6.GTwistSelmerBitsH
import Z2Z4Rank6.SparseMatrixCertificate

/-! Kernel check of the extra h-twist reconstruction matrix. -/
namespace Z2Z4Rank6.GTwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem hMatrix_sparseCertificateBlock01 : ∀ k : Fin 8,
    let i : Fin 55 := ⟨8+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul hKernelBasis hProjection i
    let lm := SparseMatrixCertificate.sparseMul hEliminator hConstraints i
    ∀ j : Fin 55, (1 : Matrix (Fin 55) (Fin 55) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.GTwistSelmer
