module

public import Z2Z4Rank6.SecondFunctionFieldCharactersFull
public import Z2Z4Rank6.SecondFunctionFieldCharactersTwistsFull
public import Mathlib.LinearAlgebra.Dimension.Localization

@[expose] public section

/-! The full eight-twist decomposition over Q(W), expressed on
point groups and their rationalizations. -/

namespace Z2Z4Rank6.SecondFunctionField
noncomputable section
open scoped TensorProduct

def fullTwistCharacterEquiv (χ : Bool × Bool × Bool) :
    (ℚ ⊗[ℤ] FullTwistCharacters.twistPoints χ) ≃ₗ[ℚ] fullCharacterSpace χ :=
  FullTwistCharacters.rationalizedTwistCharacterEquiv χ

def fullTwistDecomposition : RationalizedPoints ≃ₗ[ℚ]
    ∀ χ : Bool × Bool × Bool,ℚ ⊗[ℤ] FullTwistCharacters.twistPoints χ :=
  fullCharacterDecomposition.trans
    (LinearEquiv.piCongrRight fun χ=>(fullTwistCharacterEquiv χ).symm)

theorem group_rank_eq_rationalized_rank (G : Type*) [AddCommGroup G] :
    Module.rank ℤ G=Module.rank ℚ (ℚ ⊗[ℤ] G) := by
  calc
    Module.rank ℤ G=Module.rank ℤ (ℚ ⊗[ℤ] G) :=
      (IsLocalizedModule.rank_eq (nonZeroDivisors ℤ) le_rfl
        (TensorProduct.mk ℤ ℚ G 1)).symm
    _=Module.rank ℚ (ℚ ⊗[ℤ] G) := (IsFractionRing.rank_right_eq ℤ ℚ _).symm

theorem pointGroup_rank_full_twist_decomposition : Module.rank ℤ PointGroup=
    Cardinal.sum (fun χ : Bool × Bool × Bool=>Module.rank ℤ (FullTwistCharacters.twistPoints χ)) := by
  calc
    _=Module.rank ℚ RationalizedPoints := group_rank_eq_rationalized_rank PointGroup
    _=Module.rank ℚ (∀ χ : Bool × Bool × Bool,ℚ ⊗[ℤ] FullTwistCharacters.twistPoints χ) :=
      fullTwistDecomposition.rank_eq
    _=Cardinal.sum (fun χ : Bool × Bool × Bool=>
        Module.rank ℚ (ℚ ⊗[ℤ] FullTwistCharacters.twistPoints χ)) := rank_pi
    _=_ := by
      congr 1
      funext χ
      exact (group_rank_eq_rationalized_rank (FullTwistCharacters.twistPoints χ)).symm

end
end Z2Z4Rank6.SecondFunctionField
