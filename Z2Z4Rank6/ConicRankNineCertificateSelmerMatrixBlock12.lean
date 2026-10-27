module

public import Z2Z4Rank6.ConicRankNineCertificateSelmerData
public import Z2Z4Rank6.SparseMatrixCertificate

@[expose] public section

/-! Kernel certificate for the rank-nine conic fiber. -/
namespace Z2Z4Rank6.ConicRankNineCertificate.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem matrixBlock12 : ∀ k : Fin 4,
    let i : Fin 67 := ⟨48+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul kernelBasis projectionMatrix i
    let lm := SparseMatrixCertificate.sparseMul eliminator constraints i
    ∀ j : Fin 67,(1 : Matrix (Fin 67) (Fin 67) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.ConicRankNineCertificate.Selmer
