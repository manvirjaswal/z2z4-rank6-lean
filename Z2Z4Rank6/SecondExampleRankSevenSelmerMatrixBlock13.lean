import Z2Z4Rank6.SecondExampleRankSevenSelmerData
import Z2Z4Rank6.SparseMatrixCertificate

/-! Kernel certificate for the rank-seven second example. -/
namespace Z2Z4Rank6.SecondExampleRankSeven.Selmer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem matrixBlock13 : ∀ k : Fin 4,
    let i : Fin 61 := ⟨52+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul kernelBasis projectionMatrix i
    let lm := SparseMatrixCertificate.sparseMul eliminator constraints i
    ∀ j : Fin 61,(1 : Matrix (Fin 61) (Fin 61) (ZMod 2)) i j=np j+lm j := by
  decide +kernel
end Z2Z4Rank6.SecondExampleRankSeven.Selmer
