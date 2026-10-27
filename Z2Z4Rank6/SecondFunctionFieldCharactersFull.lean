module

public import Z2Z4Rank6.SecondFunctionFieldCharacters
public import Z2Z4Rank6.SecondFunctionFieldPointActionsFull
public import Z2Z4Rank6.ThreeCharacterDecomposition

@[expose] public section

/-! The eight-character direct sum of F(Q(G₂)) tensor Q.
The six printed sections have the four exact square-class characters
1, qA, W*qB, qA*qB. -/

namespace Z2Z4Rank6.SecondFunctionField
noncomputable section
open scoped TensorProduct DirectSum

def linearSigma1 : RationalizedPoints →ₗ[ℚ] RationalizedPoints :=
  PointScaling.rationalizeHom pointSigma1.toAddMonoidHom

theorem linearSigma1_involutive : linearSigma1.comp linearSigma1=LinearMap.id :=
  PointScaling.rationalizeHom_involutive _ pointSigma1_involutive

theorem linearSigma1_linearSigma2_commute :
    linearSigma1.comp linearSigma2=linearSigma2.comp linearSigma1 :=
  PointScaling.rationalizeHom_commute _ _ pointSigma1_pointSigma2_commute

theorem linearSigma1_linearSigma3_commute :
    linearSigma1.comp linearSigma3=linearSigma3.comp linearSigma1 :=
  PointScaling.rationalizeHom_commute _ _ pointSigma1_pointSigma3_commute

def fullCharacterSpace (χ : Bool × Bool × Bool) : Submodule ℚ RationalizedPoints :=
  ThreeCharacter.jointSpace linearSigma1 linearSigma2 linearSigma3 χ

theorem rationalPoints_mem_fullCharacterSpace (j : Fin 6) :
    rationalPoints j ∈ fullCharacterSpace (fullPointCharacter j) := by
  rw [fullCharacterSpace,ThreeCharacter.mem_jointSpace]
  have h23 := rationalPoints_mem_characterSpace j
  rw [characterSpace,Biquadratic.mem_jointSpace] at h23
  refine ⟨?_,h23⟩
  change (1 : ℚ) ⊗ₜ[ℤ] pointSigma1 (points j)=_
  rw [pointSigma1_points]
  cases h : firstPointSign j <;>
    simp [fullPointCharacter,Biquadratic.characterSign,rationalPoints,TensorProduct.tmul_neg,h]

def fullCharacterDecomposition : RationalizedPoints ≃ₗ[ℚ]
    ∀ χ : Bool × Bool × Bool,fullCharacterSpace χ :=
  ThreeCharacter.decompositionEquiv linearSigma1 linearSigma2 linearSigma3
    linearSigma1_involutive linearSigma2_involutive linearSigma3_involutive
    linearSigma1_linearSigma2_commute linearSigma1_linearSigma3_commute
    linearSigma2_linearSigma3_commute

def fullCharacterDirectSum : RationalizedPoints ≃ₗ[ℚ]
    ⨁ χ : Bool × Bool × Bool,fullCharacterSpace χ :=
  ThreeCharacter.directSumEquiv linearSigma1 linearSigma2 linearSigma3
    linearSigma1_involutive linearSigma2_involutive linearSigma3_involutive
    linearSigma1_linearSigma2_commute linearSigma1_linearSigma3_commute
    linearSigma2_linearSigma3_commute

theorem fullCharacterRankDecomposition : Module.rank ℚ RationalizedPoints=
    Cardinal.sum (fun χ : Bool × Bool × Bool=>Module.rank ℚ (fullCharacterSpace χ)) :=
  ThreeCharacter.rank_decomposition linearSigma1 linearSigma2 linearSigma3
    linearSigma1_involutive linearSigma2_involutive linearSigma3_involutive
    linearSigma1_linearSigma2_commute linearSigma1_linearSigma3_commute
    linearSigma2_linearSigma3_commute

end
end Z2Z4Rank6.SecondFunctionField
