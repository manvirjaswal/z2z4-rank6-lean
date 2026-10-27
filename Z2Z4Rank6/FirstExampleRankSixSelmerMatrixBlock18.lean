import Z2Z4Rank6.FirstExampleRankSixSelmerData
import Z2Z4Rank6.SparseMatrixCertificate

/-! Kernel certificate for the rank-six first example. -/
namespace Z2Z4Rank6.FirstExampleRankSix.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem matrixBlock18 : ∀ k : Fin 1,
    let i : Fin 73 := ⟨72+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul kernelBasis projectionMatrix i
    let lm := SparseMatrixCertificate.sparseMul eliminator constraints i
    ∀ j : Fin 73,(1 : Matrix (Fin 73) (Fin 73) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.FirstExampleRankSix.Selmer
