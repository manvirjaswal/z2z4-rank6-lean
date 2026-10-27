module

public import Z2Z4Rank6.TwistSelmerDataBitsQ2
public import Z2Z4Rank6.SparseMatrixCertificate

@[expose] public section

/-! A bounded sparse block of the binary reconstruction identity. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem q2Matrix_sparseCertificateBlock02 : ∀ k : Fin 8,
    let i : Fin 55 := ⟨16+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul q2KernelBasis q2Projection i
    let lm := SparseMatrixCertificate.sparseMul q2Eliminator q2Constraints i
    ∀ j : Fin 55, (1 : Matrix (Fin 55) (Fin 55) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.TwistSelmer
