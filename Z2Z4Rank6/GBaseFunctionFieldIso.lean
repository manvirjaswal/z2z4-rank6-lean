import Z2Z4Rank6.GBaseFunctionFieldEmbeddingData
import Z2Z4Rank6.GJacobianFunctionField
import Z2Z4Rank6.QuadraticRatFuncEquiv

/-! The G quartic field and the printed JG cubic field are
ℚ-algebra equivalent by the checked pointed-quartic coordinates and generation.
Source: Jaswal Proposition 7.2(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GBaseFunctionFieldIso
noncomputable section

theorem mapped_d : QuadraticRatFuncEquiv.baseEmbedding x x_transcendental
    GJacobianFunctionField.d=x^3+x^2-26097400*x+38851416548 := by
  simp [GJacobianFunctionField.d,map_ofNat]
theorem root_relation : y^2=QuadraticRatFuncEquiv.baseEmbedding x x_transcendental
    GJacobianFunctionField.d := equation.trans mapped_d.symm

def jacobianFunctionFieldCopyEquiv : GJacobianFunctionField.K ≃ₐ[ℚ] K :=
  QuadraticRatFuncEquiv.equiv GJacobianFunctionField.d x y x_transcendental
    root_relation field_adjoin_coordinates_eq_top
@[simp] theorem jacobianFunctionFieldCopyEquiv_x :
    jacobianFunctionFieldCopyEquiv GJacobianFunctionField.x=x :=
  QuadraticRatFuncEquiv.embedding_X GJacobianFunctionField.d x y x_transcendental root_relation
@[simp] theorem jacobianFunctionFieldCopyEquiv_y :
    jacobianFunctionFieldCopyEquiv GJacobianFunctionField.y=y :=
  QuadraticRatFuncEquiv.embedding_y GJacobianFunctionField.d x y x_transcendental root_relation

theorem jacobianFunctionFieldCopyEquiv_symm_m : jacobianFunctionFieldCopyEquiv.symm m=
    gQuarticM GJacobianFunctionField.x GJacobianFunctionField.y := by
  apply jacobianFunctionFieldCopyEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  have he := map_gQuarticM jacobianFunctionFieldCopyEquiv.toRingHom
    GJacobianFunctionField.x GJacobianFunctionField.y
  change jacobianFunctionFieldCopyEquiv
      (gQuarticM GJacobianFunctionField.x GJacobianFunctionField.y)=
    gQuarticM (jacobianFunctionFieldCopyEquiv GJacobianFunctionField.x)
      (jacobianFunctionFieldCopyEquiv GJacobianFunctionField.y) at he
  rw [he,jacobianFunctionFieldCopyEquiv_x,jacobianFunctionFieldCopyEquiv_y,m_recover]

theorem jacobianFunctionFieldCopyEquiv_symm_eta : jacobianFunctionFieldCopyEquiv.symm eta=
    gQuarticEta GJacobianFunctionField.x GJacobianFunctionField.y := by
  apply jacobianFunctionFieldCopyEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  have he := map_gQuarticEta jacobianFunctionFieldCopyEquiv.toRingHom
    GJacobianFunctionField.x GJacobianFunctionField.y
  change jacobianFunctionFieldCopyEquiv
      (gQuarticEta GJacobianFunctionField.x GJacobianFunctionField.y)=
    gQuarticEta (jacobianFunctionFieldCopyEquiv GJacobianFunctionField.x)
      (jacobianFunctionFieldCopyEquiv GJacobianFunctionField.y) at he
  rw [he,jacobianFunctionFieldCopyEquiv_x,jacobianFunctionFieldCopyEquiv_y,eta_recover]

def jacobianFunctionFieldEquiv : GJacobianFunctionField.K ≃ₐ[ℚ] GFunctionField.K :=
  jacobianFunctionFieldCopyEquiv.trans GFunctionFieldCopy.equiv

/-- The equivalence, with the original quartic field as its source. -/
def gBaseFunctionFieldEquiv : GFunctionField.K ≃ₐ[ℚ] GJacobianFunctionField.K :=
  jacobianFunctionFieldEquiv.symm

theorem gBaseFunctionFieldEquiv_m : gBaseFunctionFieldEquiv GFunctionField.m=
    gQuarticM GJacobianFunctionField.x GJacobianFunctionField.y := by
  change jacobianFunctionFieldCopyEquiv.symm (GFunctionFieldCopy.equiv.symm GFunctionField.m)=_
  have he : GFunctionFieldCopy.equiv.symm GFunctionField.m=m := by
    unfold m GFunctionFieldCopy.m; rfl
  rw [he,jacobianFunctionFieldCopyEquiv_symm_m]

theorem gBaseFunctionFieldEquiv_eta : gBaseFunctionFieldEquiv GFunctionField.eta=
    gQuarticEta GJacobianFunctionField.x GJacobianFunctionField.y := by
  change jacobianFunctionFieldCopyEquiv.symm (GFunctionFieldCopy.equiv.symm GFunctionField.eta)=_
  have he : GFunctionFieldCopy.equiv.symm GFunctionField.eta=eta := by
    unfold eta GFunctionFieldCopy.eta; rfl
  rw [he,jacobianFunctionFieldCopyEquiv_symm_eta]
end
end Z2Z4Rank6.GBaseFunctionFieldIso
