module

public import Z2Z4Rank6.TwistSelmerDataBitsQ1
public import Z2Z4Rank6.SparseMatrixCertificate

@[expose] public section

/-! A bounded sparse block of the binary reconstruction identity. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem q1Matrix_sparseCertificateBlock03 : ∀ k : Fin 8,
    let i : Fin 49 := ⟨24+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul q1KernelBasis q1Projection i
    let lm := SparseMatrixCertificate.sparseMul q1Eliminator q1Constraints i
    ∀ j : Fin 49, (1 : Matrix (Fin 49) (Fin 49) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.TwistSelmer
