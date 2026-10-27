import Z2Z4Rank6.ThirdTwistSelmer2Data
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer2
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem matrixBlock05 : ∀ k : Fin 4,
    let i : Fin 55 := ⟨20+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul kernelBasis projectionMatrix i
    let lm := SparseMatrixCertificate.sparseMul eliminator constraints i
    ∀ j : Fin 55,(1 : Matrix (Fin 55) (Fin 55) (ZMod 2)) i j=np j+lm j := by
  decide +kernel

end Z2Z4Rank6.ThirdTwist.Selmer2
