module

public import Z2Z4Rank6.BaseFunctionFieldCoordinates
public import Z2Z4Rank6.FunctionField
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

/-!
# Explicit E_C coordinates generating the function field of C

All coordinates are elements of the existing two-step quadratic field
Q(m,u,v).
-/
namespace Z2Z4Rank6
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
noncomputable section

section Membership
variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem conicM_mem (S : IntermediateField ℚ L) (t : L) (ht : t∈S) : conicM t∈S := by
  let ts : S := ⟨t,ht⟩
  exact (map_conicM S.toSubfield.subtype ts) ▸ (conicM ts).property
private theorem conicU_mem (S : IntermediateField ℚ L) (t : L) (ht : t∈S) : conicU t∈S := by
  let ts : S := ⟨t,ht⟩
  exact (map_conicU S.toSubfield.subtype ts) ▸ (conicU ts).property
private theorem conicV_mem (S : IntermediateField ℚ L) (t z : L) (ht : t∈S) (hz : z∈S) : conicV t z∈S := by
  let ts : S := ⟨t,ht⟩
  let zs : S := ⟨z,hz⟩
  exact (map_conicV S.toSubfield.subtype ts zs) ▸ (conicV ts zs).property
private theorem ecToK_mem (S : IntermediateField ℚ L) (x y : L) (hx : x∈S) (hy : y∈S) : ecToK x y∈S := by
  let xs : S := ⟨x,hx⟩
  let ys : S := ⟨y,hy⟩
  exact (map_ecToK S.toSubfield.subtype xs ys) ▸ (ecToK xs ys).property
private theorem ecToEta_mem (S : IntermediateField ℚ L) (x y : L) (hx : x∈S) (hy : y∈S) : ecToEta x y∈S := by
  let xs : S := ⟨x,hx⟩
  let ys : S := ⟨y,hy⟩
  exact (map_ecToEta S.toSubfield.subtype xs ys) ▸ (ecToEta xs ys).property
end Membership

namespace BaseFunctionFieldIso
abbrev CField := FunctionField.K
local instance baseFieldIsoCDecidableEq : DecidableEq CField := Classical.decEq _

@[irreducible] def k : CField := baseConicK FunctionField.m FunctionField.u
@[irreducible] def eta : CField := baseConicEta FunctionField.m FunctionField.u FunctionField.v

theorem m_sub_one_ne_zero : FunctionField.m-1≠0 := by
  intro h
  have he : FunctionField.m=1 := sub_eq_zero.mp h
  apply FunctionField.m_transcendental
  rw [he]
  exact isAlgebraic_one

theorem conic_den_ne_zero : k^2-15≠0 := by
  unfold k
  exact baseConic_denom_ne_zero _ _ m_sub_one_ne_zero FunctionField.u_sq

theorem quartic_equation : eta^2=quartic k := by
  unfold k eta
  exact baseConic_quartic_equation _ _ _ m_sub_one_ne_zero FunctionField.u_sq FunctionField.v_sq

theorem m_recover : conicM k=FunctionField.m := by
  unfold k
  exact baseConic_inverse_M _ _ m_sub_one_ne_zero FunctionField.u_sq

theorem u_recover : conicU k=FunctionField.u := by
  unfold k
  exact baseConic_inverse_U _ _ m_sub_one_ne_zero FunctionField.u_sq

theorem v_recover : conicV k eta=FunctionField.v := by
  unfold k eta
  exact baseConic_inverse_V _ _ _ m_sub_one_ne_zero FunctionField.u_sq

theorem k_transcendental : Transcendental ℚ k := by
  intro hk
  let S := algebraicClosure ℚ CField
  have hkS : k∈S := mem_algebraicClosure_iff.mpr hk
  have hmS := conicM_mem S k hkS
  rw [m_recover] at hmS
  exact FunctionField.m_transcendental (mem_algebraicClosure_iff.mp hmS)

def x : CField := quarticX k eta
def y : CField := quarticY k eta

theorem x_formula : quarticX k eta=x := rfl
theorem y_formula : quarticY k eta=y := rfl

theorem equation : y^2=x^3+x^2-137620*x-10504000 := by
  have he := quartic_to_ec_equation (K:=CField) k eta quartic_equation
  rw [x_formula,y_formula] at he
  exact he

theorem x_add_82_ne_zero : x+82≠0 := by
  intro hx
  rw [←x_formula] at hx
  have hk := quarticX_bad_parameter k eta quartic_equation hx
  apply k_transcendental
  rw [hk]
  have hr : IsAlgebraic ℚ (algebraMap ℚ CField (123/7)) := isAlgebraic_algebraMap _
  simpa only [map_div₀,map_ofNat] using hr

theorem k_recover : ecToK x y=k := by
  have hx := x_add_82_ne_zero
  rw [←x_formula] at hx
  have he := quartic_ec_k_inverse k eta hx
  rw [x_formula,y_formula] at he
  exact he

theorem eta_recover : ecToEta x y=eta := by
  have hx := x_add_82_ne_zero
  rw [←x_formula] at hx
  have he := quartic_ec_eta_inverse k eta hx
  rw [x_formula,y_formula] at he
  exact he

theorem x_transcendental : Transcendental ℚ x := by
  intro hx
  have hy2 : IsAlgebraic ℚ (y^2) := by
    rw [equation]
    exact (((hx.pow 3).add (hx.pow 2)).sub
      ((isAlgebraic_natCast (R:=ℚ) 137620).mul hx)).sub (isAlgebraic_natCast 10504000)
  have hy : IsAlgebraic ℚ y := hy2.of_pow (by decide : 0<(2:ℕ))
  let S := algebraicClosure ℚ CField
  have hxS : x∈S := mem_algebraicClosure_iff.mpr hx
  have hyS : y∈S := mem_algebraicClosure_iff.mpr hy
  have hkS := ecToK_mem S x y hxS hyS
  rw [k_recover] at hkS
  exact k_transcendental (mem_algebraicClosure_iff.mp hkS)

theorem field_adjoin_coordinates_eq_top : IntermediateField.adjoin ℚ ({x,y} : Set CField)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({x,y} : Set CField)
  have hxS : x∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hyS : y∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hkS := ecToK_mem S x y hxS hyS
  have heS := ecToEta_mem S x y hxS hyS
  rw [k_recover] at hkS
  rw [eta_recover] at heS
  have hmS := conicM_mem S k hkS
  have huS := conicU_mem S k hkS
  have hvS := conicV_mem S k eta hkS heS
  rw [m_recover] at hmS
  rw [u_recover] at huS
  rw [v_recover] at hvS
  have hle : IntermediateField.adjoin ℚ
      ({FunctionField.m,FunctionField.u,FunctionField.v} : Set CField)≤S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hmS
    · exact huS
    · exact hvS
  rw [FunctionField.field_adjoin_coordinates_eq_top] at hle
  exact top_unique hle

end BaseFunctionFieldIso
end
end Z2Z4Rank6
