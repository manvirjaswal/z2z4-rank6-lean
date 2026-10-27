import Z2Z4Rank6.ThirdTwistFieldTwistCharacters
import Mathlib.LinearAlgebra.Dimension.Localization

/-! The full eight-twist decomposition over Q(W), expressed on
point groups and their rationalizations. -/

namespace Z2Z4Rank6.ThirdTwistField
noncomputable section
open scoped TensorProduct

abbrev RationalizedPoints := ℚ ⊗[ℤ] PointGroup

def fullCharacterDecomposition : RationalizedPoints ≃ₗ[ℚ]
    ∀ χ : Bool × Bool × Bool,TwistCharacters.fullCharacterSpace χ :=
  ThreeCharacter.decompositionEquiv
    (PointScaling.rationalizeHom pointSigmaU.toAddMonoidHom)
    (PointScaling.rationalizeHom pointSigmaV.toAddMonoidHom)
    (PointScaling.rationalizeHom pointSigmaW.toAddMonoidHom)
    (PointScaling.rationalizeHom_involutive _ pointSigmaU_involutive)
    (PointScaling.rationalizeHom_involutive _ pointSigmaV_involutive)
    (PointScaling.rationalizeHom_involutive _ pointSigmaW_involutive)
    (PointScaling.rationalizeHom_commute _ _ pointSigmaU_pointSigmaV_commute)
    (PointScaling.rationalizeHom_commute _ _ pointSigmaU_pointSigmaW_commute)
    (PointScaling.rationalizeHom_commute _ _ pointSigmaV_pointSigmaW_commute)

def fullTwistCharacterEquiv (χ : Bool × Bool × Bool) :
    (ℚ ⊗[ℤ] TwistCharacters.twistPoints χ) ≃ₗ[ℚ] TwistCharacters.fullCharacterSpace χ :=
  TwistCharacters.rationalizedTwistCharacterEquiv χ

def fullTwistDecomposition : RationalizedPoints ≃ₗ[ℚ]
    ∀ χ : Bool × Bool × Bool,ℚ ⊗[ℤ] TwistCharacters.twistPoints χ :=
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
    Cardinal.sum (fun χ : Bool × Bool × Bool=>Module.rank ℤ (TwistCharacters.twistPoints χ)) := by
  calc
    _=Module.rank ℚ RationalizedPoints := group_rank_eq_rationalized_rank PointGroup
    _=Module.rank ℚ (∀ χ : Bool × Bool × Bool,ℚ ⊗[ℤ] TwistCharacters.twistPoints χ) :=
      fullTwistDecomposition.rank_eq
    _=Cardinal.sum (fun χ : Bool × Bool × Bool=>
        Module.rank ℚ (ℚ ⊗[ℤ] TwistCharacters.twistPoints χ)) := rank_pi
    _=_ := by
      congr 1
      funext χ
      exact (group_rank_eq_rationalized_rank (TwistCharacters.twistPoints χ)).symm

end
end Z2Z4Rank6.ThirdTwistField
