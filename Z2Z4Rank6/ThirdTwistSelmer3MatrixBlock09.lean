module

public import Z2Z4Rank6.ThirdTwistSelmer3Data
public import Z2Z4Rank6.TwistSelmerConstraintEntry

@[expose] public section

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem matrixBlock09 : ∀ k : Fin 4,
    let i : Fin 61 := ⟨36+k.val,by omega⟩
    let np := SparseMatrixCertificate.sparseMul kernelBasis projectionMatrix i
    let lm := SparseMatrixCertificate.sparseMul eliminator constraints i
    ∀ j : Fin 61,(1 : Matrix (Fin 61) (Fin 61) (ZMod 2)) i j=np j+lm j := by
  decide +kernel

end Z2Z4Rank6.ThirdTwist.Selmer3
