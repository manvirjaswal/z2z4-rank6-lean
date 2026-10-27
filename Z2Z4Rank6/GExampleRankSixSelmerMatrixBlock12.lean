module

public import Z2Z4Rank6.GExampleRankSixSelmerData
public import Z2Z4Rank6.SparseMatrixCertificate

@[expose] public section

/-! Kernel certificate for the rank-six G-fiber example. -/
namespace Z2Z4Rank6.GExampleRankSix.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem matrixBlock12 : ∀ k : Fin 4,
    let i : Fin 55 := ⟨48+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul kernelBasis projectionMatrix i
    let lm := SparseMatrixCertificate.sparseMul eliminator constraints i
    ∀ j : Fin 55,(1 : Matrix (Fin 55) (Fin 55) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.GExampleRankSix.Selmer
