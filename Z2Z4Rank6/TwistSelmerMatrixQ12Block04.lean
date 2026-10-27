import Z2Z4Rank6.TwistSelmerDataBitsQ12
import Z2Z4Rank6.SparseMatrixCertificate

/-! A bounded sparse block of the binary reconstruction identity. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem q12Matrix_sparseCertificateBlock04 : ∀ k : Fin 8,
    let i : Fin 58 := ⟨32+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul q12KernelBasis q12Projection i
    let lm := SparseMatrixCertificate.sparseMul q12Eliminator q12Constraints i
    ∀ j : Fin 58, (1 : Matrix (Fin 58) (Fin 58) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.TwistSelmer
