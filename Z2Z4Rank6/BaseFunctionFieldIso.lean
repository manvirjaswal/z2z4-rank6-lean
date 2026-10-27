module

public import Z2Z4Rank6.BaseFunctionFieldEmbeddingData
public import Z2Z4Rank6.ECFunctionField

@[expose] public section

/-!
# A Q-algebra isomorphism Q(E_C) ≃ Q(C)

The map is constructed by evaluation of rational functions followed by the
quadratic root-algebra universal property. Explicit inverse coordinates prove
that its image contains all three generators m,u,v of Q(C).
-/
namespace Z2Z4Rank6.BaseFunctionFieldIso
noncomputable section
open Polynomial
local instance baseFunctionFieldIsoDecidableEq : DecidableEq CField := Classical.decEq _

def baseRingEmbedding : ECFunctionField.Base →+* CField :=
  RatFunc.liftRingHom (aeval x).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp x_transcendental))

def baseEmbedding : ECFunctionField.Base →ₐ[ℚ] CField where
  __ := baseRingEmbedding
  commutes' := baseRingEmbedding.map_rat_algebraMap

@[simp] theorem baseRingEmbedding_X : baseRingEmbedding RatFunc.X=x := by
  unfold baseRingEmbedding
  rw [RatFunc.liftRingHom_X]
  simp

@[simp] theorem baseEmbedding_X : baseEmbedding RatFunc.X=x := baseRingEmbedding_X

theorem baseRingEmbedding_d : baseRingEmbedding ECFunctionField.d=x^3+x^2-137620*x-10504000 := by
  simp [ECFunctionField.d,map_ofNat]

def ecToCRingHom : ECFunctionField.K →+* CField := by
  letI : Algebra ECFunctionField.Base CField := baseRingEmbedding.toAlgebra
  refine (QuadraticAlgebra.lift (R:=ECFunctionField.Base) (A:=CField) ⟨y,?_⟩).toRingHom
  change y*y=baseRingEmbedding ECFunctionField.d*1+baseRingEmbedding 0*y
  simp only [map_zero,zero_mul,add_zero,mul_one]
  rw [baseRingEmbedding_d,←sq]
  exact equation

def ecToCFunctionField : ECFunctionField.K →ₐ[ℚ] CField where
  __ := ecToCRingHom
  commutes' := ecToCRingHom.map_rat_algebraMap

@[simp] theorem ecToCFunctionField_x : ecToCFunctionField ECFunctionField.x=x := by
  change baseRingEmbedding RatFunc.X*1+baseRingEmbedding 0*y=x
  simp only [map_zero,zero_mul,add_zero,mul_one,baseRingEmbedding_X]

@[simp] theorem ecToCFunctionField_y : ecToCFunctionField ECFunctionField.y=y := by
  change baseRingEmbedding 0*1+baseRingEmbedding 1*y=y
  simp only [map_zero,map_one,zero_mul,one_mul,zero_add]

theorem ecToCFunctionField_surjective : Function.Surjective ecToCFunctionField := by
  have hx : x∈ecToCFunctionField.fieldRange := ⟨ECFunctionField.x,ecToCFunctionField_x⟩
  have hy : y∈ecToCFunctionField.fieldRange := ⟨ECFunctionField.y,ecToCFunctionField_y⟩
  have hle : IntermediateField.adjoin ℚ ({x,y}:Set CField)≤ecToCFunctionField.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  rw [field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

/-- The algebraic function fields of the printed cubic and the
three-equation base C are Q-algebra isomorphic, by the displayed maps. -/
def ecFunctionFieldEquiv : ECFunctionField.K ≃ₐ[ℚ] FunctionField.K :=
  AlgEquiv.ofBijective ecToCFunctionField ⟨ecToCFunctionField.injective,ecToCFunctionField_surjective⟩

@[simp] theorem ecFunctionFieldEquiv_x : ecFunctionFieldEquiv ECFunctionField.x=quarticX k eta :=
  ecToCFunctionField_x
@[simp] theorem ecFunctionFieldEquiv_y : ecFunctionFieldEquiv ECFunctionField.y=quarticY k eta :=
  ecToCFunctionField_y

theorem ecFunctionFieldEquiv_symm_k : ecFunctionFieldEquiv.symm k=
    ecToK ECFunctionField.x ECFunctionField.y := by
  apply ecFunctionFieldEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  have he := map_ecToK ecFunctionFieldEquiv.toRingHom ECFunctionField.x ECFunctionField.y
  change ecFunctionFieldEquiv (ecToK ECFunctionField.x ECFunctionField.y)=
    ecToK (ecFunctionFieldEquiv ECFunctionField.x) (ecFunctionFieldEquiv ECFunctionField.y) at he
  rw [he]
  have hx : ecFunctionFieldEquiv ECFunctionField.x=x := ecToCFunctionField_x
  have hy : ecFunctionFieldEquiv ECFunctionField.y=y := ecToCFunctionField_y
  rw [hx,hy,k_recover]

theorem ecFunctionFieldEquiv_symm_eta : ecFunctionFieldEquiv.symm eta=
    ecToEta ECFunctionField.x ECFunctionField.y := by
  apply ecFunctionFieldEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  have he := map_ecToEta ecFunctionFieldEquiv.toRingHom ECFunctionField.x ECFunctionField.y
  change ecFunctionFieldEquiv (ecToEta ECFunctionField.x ECFunctionField.y)=
    ecToEta (ecFunctionFieldEquiv ECFunctionField.x) (ecFunctionFieldEquiv ECFunctionField.y) at he
  rw [he]
  have hx : ecFunctionFieldEquiv ECFunctionField.x=x := ecToCFunctionField_x
  have hy : ecFunctionFieldEquiv ECFunctionField.y=y := ecToCFunctionField_y
  rw [hx,hy,eta_recover]

theorem ecFunctionFieldEquiv_symm_m : ecFunctionFieldEquiv.symm FunctionField.m=
    conicM (ecToK ECFunctionField.x ECFunctionField.y) := by
  rw [←m_recover]
  have he := map_conicM ecFunctionFieldEquiv.symm.toRingHom k
  change ecFunctionFieldEquiv.symm (conicM k)=conicM (ecFunctionFieldEquiv.symm k) at he
  rw [he,ecFunctionFieldEquiv_symm_k]

theorem ecFunctionFieldEquiv_symm_u : ecFunctionFieldEquiv.symm FunctionField.u=
    conicU (ecToK ECFunctionField.x ECFunctionField.y) := by
  rw [←u_recover]
  have he := map_conicU ecFunctionFieldEquiv.symm.toRingHom k
  change ecFunctionFieldEquiv.symm (conicU k)=conicU (ecFunctionFieldEquiv.symm k) at he
  rw [he,ecFunctionFieldEquiv_symm_k]

theorem ecFunctionFieldEquiv_symm_v : ecFunctionFieldEquiv.symm FunctionField.v=
    conicV (ecToK ECFunctionField.x ECFunctionField.y)
      (ecToEta ECFunctionField.x ECFunctionField.y) := by
  rw [←v_recover]
  have he := map_conicV ecFunctionFieldEquiv.symm.toRingHom k eta
  change ecFunctionFieldEquiv.symm (conicV k eta)=
    conicV (ecFunctionFieldEquiv.symm k) (ecFunctionFieldEquiv.symm eta) at he
  rw [he,ecFunctionFieldEquiv_symm_k,ecFunctionFieldEquiv_symm_eta]

/-- The same field isomorphism, oriented from Q(C) to Q(E_C). -/
def baseFunctionFieldEquiv : FunctionField.K ≃ₐ[ℚ] ECFunctionField.K := ecFunctionFieldEquiv.symm

end
end Z2Z4Rank6.BaseFunctionFieldIso
