import Z2Z4Rank6.GQuadraticCharacters
import Z2Z4Rank6.GQuadraticLinear
import Z2Z4Rank6.FunctionFieldFiniteGeneration
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The quadratic rank decomposition over Q(G)

Proposition 7.2(b) of Jaswal, DOI: 10.5281/zenodo.23437117. The two
base point groups rationalize to the two conjugation spaces.
-/

namespace Z2Z4Rank6.GFunctionField.QuadraticCharacters

open scoped TensorProduct
noncomputable section

abbrev RationalizedPoints := ℚ ⊗[ℤ] PointGroup

def linearConjugation : RationalizedPoints →ₗ[ℚ] RationalizedPoints :=
  PointScaling.rationalizeHom pointConjugation.toAddMonoidHom

theorem linearConjugation_involutive :
    linearConjugation.comp linearConjugation=LinearMap.id :=
  PointScaling.rationalizeHom_involutive _ pointConjugation_involutive

def characterSpace (ε : Bool) : Submodule ℚ RationalizedPoints :=
  QuadraticLinear.signSpace linearConjugation ε

private theorem rationalize_id (G : Type*) [AddCommGroup G] :
    PointScaling.rationalizeHom (AddMonoidHom.id G)=LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul q P => rfl
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx,hy]

def rationalizedTwistCharacterEquiv (ε : Bool) :
    (ℚ ⊗[ℤ] (twistCurve ε).toAffine.Point) ≃ₗ[ℚ] characterSpace ε := by
  have e : (ℚ ⊗[ℤ] characterSubgroup ε) ≃ₗ[ℚ] characterSpace ε := by
    have e0 := CharacterRationalization.equivCharacterSpace pointConjugation.toAddMonoidHom
      (AddMonoidHom.id PointGroup) pointConjugation_involutive
      (fun _ => rfl) (fun _ => rfl) (ε,false)
    rw [rationalize_id PointGroup] at e0
    exact e0
  exact (PointScaling.rationalizeEquiv (characterEquiv ε)).trans e

/-- The rationalized Q(G) group is the product of the original and
h-twisted rationalized Q(m) groups. -/
def quadraticDecomposition : RationalizedPoints ≃ₗ[ℚ]
    (ℚ ⊗[ℤ] (twistCurve false).toAffine.Point) ×
      (ℚ ⊗[ℤ] (twistCurve true).toAffine.Point) :=
  (QuadraticLinear.decompositionEquiv linearConjugation linearConjugation_involutive).trans
    ((rationalizedTwistCharacterEquiv false).symm.prodCongr
      (rationalizedTwistCharacterEquiv true).symm)

private theorem group_rank_eq_rationalized_rank (G : Type*) [AddCommGroup G] :
    Module.rank ℤ G=Module.rank ℚ (ℚ ⊗[ℤ] G) := by
  calc
    Module.rank ℤ G=Module.rank ℤ (ℚ ⊗[ℤ] G) :=
      (IsLocalizedModule.rank_eq (nonZeroDivisors ℤ) le_rfl (TensorProduct.mk ℤ ℚ G 1)).symm
    _ = Module.rank ℚ (ℚ ⊗[ℤ] G) :=
      (IsFractionRing.rank_right_eq ℤ ℚ (ℚ ⊗[ℤ] G)).symm

theorem pointGroup_rank_twist_decomposition : Module.rank ℤ PointGroup=
    Module.rank ℤ (twistCurve false).toAffine.Point+
      Module.rank ℤ (twistCurve true).toAffine.Point := by
  rw [group_rank_eq_rationalized_rank PointGroup,quadraticDecomposition.rank_eq,rank_prod']
  rw [←group_rank_eq_rationalized_rank,←group_rank_eq_rationalized_rank]

/-- The rank identity for the precise original and h-twist models used in
the arithmetic bounds. -/
theorem pointGroup_rank_decomposition : Module.rank ℤ PointGroup=
    Module.rank ℤ RationalFunctionFamily.curve.toAffine.Point+
      Module.rank ℤ (GusicTadic.genericModel GTwistSelmer.hPolynomial).toAffine.Point := by
  rw [pointGroup_rank_twist_decomposition]
  have h0 := (PointScaling.pointCongr twistCurve_false).toIntLinearEquiv.rank_eq
  have h1 := (PointScaling.pointCongr twistCurve_true).toIntLinearEquiv.rank_eq
  rw [h0,h1]

theorem field_finitely_generated : (⊤ : IntermediateField ℚ K).FG := by
  rw [←field_adjoin_coordinates_eq_top]
  exact IntermediateField.fg_adjoin_of_finite (by simp)

theorem pointGroup_finitely_generated (hMWLN : MordellWeilLangNeronTheorem.{0}) :
    AddGroup.FG PointGroup :=
  hMWLN K field_finitely_generated (X m) genericFiberElliptic

theorem pointGroup_moduleFinite (hMWLN : MordellWeilLangNeronTheorem.{0}) :
    Module.Finite ℤ PointGroup :=
  Module.Finite.iff_addGroup_fg.mpr (pointGroup_finitely_generated hMWLN)

end
end Z2Z4Rank6.GFunctionField.QuadraticCharacters
